// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![forbid(
    unsafe_code, // Do not introduce unsafe code into this crate.
)]
#![deny(
    bare_trait_objects,             // Use the 'dyn' keyword.
    unused_extern_crates,           // Don't add unnecessary dependencies.
)]
#![warn(
    unused_qualifications,  // Please don't clutter code with paths.
)]

use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashSet;
use std::convert::TryFrom;
use syn::punctuated::Punctuated;
use syn::{parse_quote, Token};

#[proc_macro_derive(Bits, attributes(vec_order, unimplemented))]
pub fn bits_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();

    let type_name = &ast.ident;

    let expanded = match ast.data {
        syn::Data::Enum(ref e) => derive_enum(type_name, &ast.generics, e),
        syn::Data::Struct(ref s) => derive_struct(type_name, &ast.generics, &ast.attrs, s),
        _ => panic!("Bad type for bits_derive"),
    };

    expanded.into()
}

/// A helper that adds a set of types to the generic clause, constraining all of
/// them to be instances of `Bits`.
fn bits_impl_generics(generics: &syn::Generics, req_types: &HashSet<syn::Type>) -> syn::Generics {
    let mut generics = generics.clone();

    generics.where_clause = Some({
        let where_token = Token![where](Span::call_site());
        let mut predicates = generics
            .where_clause
            .map(|c| c.predicates)
            .unwrap_or_default();

        for req_type in req_types.iter() {
            predicates.push(parse_quote! {
                #req_type: ::bits::Bits
            });
        }

        syn::WhereClause {
            where_token,
            predicates,
        }
    });

    generics
}

fn derive_enum(type_name: &Ident, generics: &syn::Generics, e: &syn::DataEnum) -> TokenStream {
    // TODO When [`proc_macro::Span::def_site()][1] will stabilize, these should
    // be transformed to use the `def_site()` constructor to generate hygienic
    // names.  Our best bet for now it to use long names and hope we would not
    // have a collision.
    //
    // [1]: https://doc.rust-lang.org/stable/proc_macro/struct.Span.html#method.def_site
    let bits = quote! { __bits_derive_bits };
    let disc = quote! { __bits_derive_disc };
    let dst = quote! { __bits_derive_dst };
    let max_field_bits = quote! { __bits_derive_max_field_bits };

    // Encoded enums consist of two parts: the discriminant and the fields.
    //
    // The discriminant distinguishes between the variants of the enum. Its
    // value is simply the index of the variant in declaration order; it's
    // packed into as the least number of bits required to represent all
    // variants. (It may be zero bits for a single-variant enum.)
    //
    // The fields section is long enough to represent the encoded field tuple of
    // any variant. Its size is chosen by the longest variant. Within a variant,
    // the fields are encoded as for a tuple, and are right-justified toward the
    // LSB.
    //
    // Unused bits between a discriminator and the top bit of fields (for
    // variants shorter than the longest) are undefined: generated as zero,
    // ignored on parsing.

    let n = e.variants.len();
    let disc_bits = bit_size(n - 1);

    let no_explicit_discriminants = e.variants.iter().all(|v| v.discriminant.is_none());
    if !no_explicit_discriminants {
        panic!("I can't handle enums with explicit discriminants");
    }

    let mut cases_unpack = vec![];
    let mut cases_pack = vec![];
    let mut size_exprs = vec![];
    let mut req_types = HashSet::new();

    for (i, v) in e.variants.iter().enumerate() {
        let name = &v.ident;
        let idx = Literal::u64_suffixed(i as u64);
        let unpack_panic = v
            .attrs
            .iter()
            .any(|a| a.parse_meta().unwrap().path().is_ident("unimplemented"));
        let (quote_unpack, quote_pack, field_types) = match &v.fields {
            // A unit variant has no fields.
            syn::Fields::Unit => (
                quote! {
                    #idx => #type_name::#name,
                },
                quote! {
                    #type_name::#name => {
                        use ::bits::reexport::bitvec::field::BitField;
                        #dst[#max_field_bits ..].store_le(#idx);
                        #dst[.. #max_field_bits].fill(false);
                    }
                },
                vec![],
            ),

            // An enum with unnamed (tuple-style) fields.
            syn::Fields::Unnamed(u) => generate_enum_fields(
                i,
                type_name,
                name,
                &mut size_exprs,
                &u.unnamed,
                false,
                unpack_panic,
            ),

            // An enum with named (struct-style) fields.
            syn::Fields::Named(n) => generate_enum_fields(
                i,
                type_name,
                name,
                &mut size_exprs,
                &n.named,
                true,
                unpack_panic,
            ),
        };
        cases_unpack.push(quote_unpack);
        cases_pack.push(quote_pack);
        req_types.extend(field_types);
    }

    // If the enum contained only unit variants, size_exprs will be empty. Stuff
    // it with zero to simplify the code below.
    if size_exprs.is_empty() {
        size_exprs.push(quote! { 0 })
    }

    // Compute the length of the field section as a chained `max` expression.
    let max_field_bits_expr = {
        let mut size_exprs = size_exprs.into_iter();
        let mut max_expr = size_exprs.next().unwrap();
        for size_expr in size_exprs {
            max_expr = quote! { ::bits::const_max(#max_expr, #size_expr) }
        }
        max_expr
    };

    // This is a bit tricky: we want to parametrize `#type_name` using the
    // specified generic parameters, but we also need to add `Bits` constraints
    // to a number of types.
    let bits_generics = bits_impl_generics(generics, &req_types);
    let (impl_generics, _ty_generics, where_clause) = bits_generics.split_for_impl();
    let (_impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let bitstore_ty = quote! { ::bits::reexport::bitvec::store::BitStore };

    quote! {
        #[cfg_attr(feature = "cargo-clippy", allow(double_parens))]
        impl #impl_generics ::bits::Bits
            for #type_name #ty_generics
        #where_clause
        {
            const SIZE: usize = #disc_bits + #max_field_bits_expr;

            #[inline]
            fn unpack<__BitsS: #bitstore_ty>(#bits: &::bits::Slice<__BitsS>) -> Self {
                let expected_size =
                    <Self as ::bits::Bits>::SIZE;
                assert!(
                    #bits.len() == expected_size,
                    "{}::unpack(): Bit size mismatch.\n\
                     Expected bit size: {}\n\
                     Actual bit size: {}",
                    stringify!(#type_name),
                    expected_size,
                    #bits.len(),
                );

                let #max_field_bits = #max_field_bits_expr;
                let #disc: u64 = {
                    use ::bits::reexport::bitvec::field::BitField;
                    #bits[#max_field_bits ..].load_le()
                };

                let #bits = &#bits[.. #max_field_bits];
                match #disc {
                    #( #cases_unpack )*
                    _ => panic!("bad encoding for {}: {},{}",
                                stringify!(#type_name #generics),
                                #disc, #bits),
                }
            }

            #[inline]
            fn pack_to<__BitsS: #bitstore_ty>(&self, #dst: &mut ::bits::Slice<__BitsS>) {
                let expected_size =
                    <Self as ::bits::Bits>::SIZE;
                assert!(
                    #dst.len() == expected_size,
                    "{}::pack_to(): Bit size mismatch.\n\
                     Expected bit size: {}\n\
                     Actual bit size: {}",
                    stringify!(#type_name),
                    expected_size,
                    #dst.len(),
                );

                let #max_field_bits = #max_field_bits_expr;
                match self {
                    #( #cases_pack )*
                }
            }
        }
    }
}

fn in_brackets<I>(braces: bool, vals: I) -> TokenStream
where
    I: Iterator<Item = TokenStream>,
{
    if braces {
        quote! {{#(#vals),*}}
    } else {
        quote! {(#(#vals),*)}
    }
}

#[allow(clippy::too_many_arguments)]
fn generate_enum_fields(
    disc: usize,
    type_name: &Ident,
    name: &Ident,
    size_exprs: &mut Vec<TokenStream>,
    fields: &Punctuated<syn::Field, syn::token::Comma>,
    braces: bool,
    unpack_panic: bool,
) -> (TokenStream, TokenStream, Vec<syn::Type>) {
    // TODO When [`proc_macro::Span::def_site()][1] will stabilize, these should
    // be transformed to use the `def_site()` constructor to generate hygienic
    // names.  Our best bet for now it to use long names and hope we would not
    // have a collision.
    //
    // [1]: https://doc.rust-lang.org/stable/proc_macro/struct.Span.html#method.def_site
    let bits = quote! { __bits_derive_bits };
    let component_end = quote! { __bits_derive_component_end };
    let component_start = quote! { __bits_derive_component_start };
    let dst = quote! { __bits_derive_dst };
    let max_field_bits = quote! { __bits_derive_max_field_bits };
    let tu = quote! { __bits_derive_tu };

    let field_types_vec: Vec<_> = fields.iter().map(|f| f.ty.clone()).collect();
    let field_types: &[_] = &field_types_vec;

    let size_expr = quote! {
        0 #(+ <#field_types as ::bits::Bits>::SIZE)*
    };
    size_exprs.push(size_expr.clone());

    let ctor_fields = in_brackets(
        braces,
        fields.iter().enumerate().map(|(i, f)| {
            let idx = syn::Index::from(i);
            if let Some(ref n) = f.ident {
                quote! { #n: #tu.#idx }
            } else {
                quote! { #tu.#idx }
            }
        }),
    );

    let constructed_value = quote! { #type_name::#name #ctor_fields };

    let use_value = if unpack_panic {
        quote! { panic!("Unimplemented variant {:?}", #constructed_value); }
    } else {
        constructed_value
    };

    let idx = Literal::u64_suffixed(disc as u64);
    let q_unpack = {
        let field_types = &field_types;
        quote! {
            #idx => {
                let #tu: (#(#field_types,)*) =
                    ::bits::Bits::unpack(
                        &#bits[ .. #size_expr]
                    );
                #use_value
            },
        }
    };

    // Field names for a struct or tuple.
    // If it's a struct, use the struct's field names.
    // If it's a tuple, build names t0, t1,... tN-1
    let fields_vec: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let n = if braces {
                f.ident.clone().unwrap()
            } else {
                format_ident!("t{}", i)
            };
            quote! { #n }
        })
        .collect();
    let fields: &[_] = &fields_vec;

    // The elements part of a struct or tuple pattern match, ie {bar, baz} or (t0, t1)
    let pattern_elems = in_brackets(braces, fields.iter().cloned());

    let q_pack = quote! {
        #type_name::#name #pattern_elems => {
            use ::bits::reexport::bitvec::field::BitField;
            #dst[#max_field_bits..].store_le(#idx);
            let mut #component_end = #size_expr;
            #(
                let #component_start = #component_end
                    - <#field_types as ::bits::Bits>::SIZE;
                #fields.pack_to(&mut #dst[#component_start .. #component_end]);
                #component_end = #component_start;
            )*
            let _unused = #component_end; // Suppress warning
        },
    };
    (q_unpack, q_pack, field_types_vec)
}

fn derive_struct(
    type_name: &Ident,
    generics: &syn::Generics,
    attrs: &[syn::Attribute],
    s: &syn::DataStruct,
) -> TokenStream {
    // TODO When [`proc_macro::Span::def_site()][1] will stabilize, these should
    // be transformed to use the `def_site()` constructor to generate hygienic
    // names.  Our best bet for now it to use long names and hope we would not
    // have a collision.
    //
    // [1]: https://doc.rust-lang.org/stable/proc_macro/struct.Span.html#method.def_site
    let bits = quote! { __bits_derive_bits };
    let dst = quote! { __bits_derive_dst };

    // A struct is encoded like a struct-variant enum with only one
    // variant. The fields are concatenated in the order defined, unless the
    // `vec_order` attr appears, in which case they're reversed.
    let vec_order = attrs
        .iter()
        .any(|a| a.parse_meta().unwrap().path().is_ident("vec_order"));

    let (quote_unpack, quote_pack, req_types, size_expr) = match &s.fields {
        // A unit variant has no fields.
        syn::Fields::Unit => (
            quote! {
                #type_name
            },
            quote! {
                0
            },
            HashSet::new(),
            quote! { 0 },
        ),

        // A tuple-style struct (fields don't have names)
        syn::Fields::Unnamed(u) => generate_struct_fields(type_name, &u.unnamed, vec_order, false),

        // A normal struct (fields have names)
        syn::Fields::Named(n) => generate_struct_fields(type_name, &n.named, vec_order, true),
    };

    // This is a bit tricky: we want to parametrize `#type_name` using the
    // specified generic parameters, but we also need to add `Bits` constraints
    // to a number of types.
    let bits_generics = bits_impl_generics(generics, &req_types);
    let (impl_generics, _ty_generics, where_clause) = bits_generics.split_for_impl();
    let (_impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let bitstore_ty = quote! { ::bits::reexport::bitvec::store::BitStore };

    quote! {
        impl #impl_generics ::bits::Bits
            for #type_name #ty_generics #where_clause {
            const SIZE: usize = #size_expr;

            #[inline]
            fn unpack<__BitsS: #bitstore_ty>(#bits: &::bits::Slice<__BitsS>) -> Self {
                let expected_size =
                    <Self as ::bits::Bits>::SIZE;
                assert!(
                    #bits.len() == expected_size,
                    "{}::unpack(): Bit size mismatch.\n\
                     Expected bit size: {}\n\
                     Actual bit size: {}",
                    stringify!(#type_name),
                    expected_size,
                    #bits.len(),
                );

                #quote_unpack
            }

            #[inline]
            fn pack_to<__BitsS: #bitstore_ty>(&self, #dst: &mut ::bits::Slice<__BitsS>) {
                let expected_size =
                    <Self as ::bits::Bits>::SIZE;
                assert!(
                    #dst.len() == expected_size,
                    "{}::pack_to(): Bit size mismatch.\n\
                     Expected bit size: {}\n\
                     Actual bit size: {}",
                    stringify!(#type_name),
                    expected_size,
                    #dst.len(),
                );

                #quote_pack
            }
        }
    }
}

fn generate_struct_fields(
    type_name: &Ident,
    fields: &Punctuated<syn::Field, syn::token::Comma>,
    vec_order: bool,
    braces: bool,
) -> (TokenStream, TokenStream, HashSet<syn::Type>, TokenStream) {
    // TODO When [`proc_macro::Span::def_site()][1] will stabilize, these should
    // be transformed to use the `def_site()` constructor to generate hygienic
    // names.  Our best bet for now it to use long names and hope we would not
    // have a collision.
    //
    // [1]: https://doc.rust-lang.org/stable/proc_macro/struct.Span.html#method.def_site
    let bits = quote! { __bits_derive_bits };
    let component_end = quote! { __bits_derive_component_end };
    let component_start = quote! { __bits_derive_component_start };
    let dst = quote! { __bits_derive_dst };
    let tu = quote! { __bits_derive_tu };

    let mut field_types_vec: Vec<_> = fields.iter().map(|f| f.ty.clone()).collect();
    if vec_order {
        field_types_vec.reverse();
    }
    let field_types: &[_] = &field_types_vec;

    let size_expr = quote! {
        0 #(+ <#field_types as ::bits::Bits>::SIZE)*
    };

    let n = field_types.len();
    let ctor_fields = in_brackets(
        braces,
        fields.iter().enumerate().map(|(i, f)| {
            let ti = syn::Index::from(if vec_order { n - 1 - i } else { i });

            if let Some(ref name) = f.ident {
                quote! { #name: #tu.#ti }
            } else {
                quote! { #tu.#ti }
            }
        }),
    );
    let mut accessors: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, f)| {
            if let Some(ref name) = f.ident {
                quote! { self.#name }
            } else {
                let ti = syn::Index::from(i);
                quote! { self.#ti }
            }
        })
        .collect();
    if vec_order {
        accessors.reverse();
    }

    let q_unpack = {
        let field_types = &field_types;
        quote! {
            let #tu: (#(#field_types,)*) =
                ::bits::Bits::unpack(#bits);
            #type_name #ctor_fields
        }
    };
    let q_pack = quote! {
        let mut #component_end = #size_expr;
        #(
            let #component_start = #component_end
                - <#field_types as ::bits::Bits>::SIZE;
            #accessors.pack_to(&mut #dst[#component_start .. #component_end]);
            #component_end = #component_start;
        )*
        let _unused = #component_end; // Suppress warning
    };
    (
        q_unpack,
        q_pack,
        field_types_vec.into_iter().collect::<HashSet<_>>(),
        size_expr,
    )
}

/// Determines the number of bits required to represent `x`.
fn bit_size(x: usize) -> usize {
    let x = x as u64; // Number of bits now predictable
    usize::try_from(64 - x.leading_zeros()).unwrap()
}
