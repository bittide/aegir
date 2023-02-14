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

#![allow(unused_imports)]
extern crate proc_macro;
use proc_macro2::{Span, TokenStream};
use proc_macro_error::{abort, proc_macro_error};
use quote::{quote, quote_spanned};
use std::collections::HashMap;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::{
    parse_macro_input, parse_quote, Attribute, Data, DeriveInput, Field, Fields, GenericParam,
    Generics, Ident, Index, Meta, NestedMeta, PathArguments, Type, TypePath,
};
#[proc_macro_error]
#[proc_macro_derive(HasSchema, attributes(schema_opaque))]
pub fn derive_schema(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    // Add a bound `T: HasSchema` to every type parameter T.
    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let ty_param_calls = generics.type_params().map(|ty_param| {
        let ty = &ty_param.ident;
        quote_spanned!(ty.span()=> &<#ty as ::schema::HasSchema>::TY)
    });
    check_no_serde(&input.attrs);
    let (body, child_field_bundles) = if is_opaque(&input.attrs) {
        (quote!(::schema::Body::Opaque(0)), quote!())
    } else {
        match input.data {
            Data::Struct(s) => {
                let (body, child_field_bundles) = fields_to_body_and_children(s.fields);
                (
                    quote! { ::schema::Body::Struct(#body) },
                    child_field_bundles,
                )
            }
            Data::Enum(e) => {
                let mut all_child_field_bundles = Vec::new();
                let mut variants = Vec::new();
                for v in e.variants {
                    check_no_serde(&v.attrs);
                    let (body, child_field_bundles) = fields_to_body_and_children(v.fields);
                    let vname = v.ident.to_string();
                    variants.push(quote!(::schema::Variant{name: #vname, fields: #body}));
                    all_child_field_bundles.push(child_field_bundles);
                }
                (
                    quote! { ::schema::Body::Enum(&[ #(#variants),* ]) },
                    quote! { #(#all_child_field_bundles)* },
                )
            }
            Data::Union(u) => abort!(
                u.union_token.span,
                "HasSchema only works on structs and enums"
            ),
        }
    };
    let full_name = quote! {
        ::std::concat!(::std::module_path!(), "::", ::std::stringify!(#name))
    };
    let expanded = quote! {
        impl #impl_generics ::schema::HasSchema
                for #name #ty_generics #where_clause {
            const TY: ::schema::Ty =
                ::schema::Ty{
                    name: #full_name,
                    args: &[ #(#ty_param_calls),* ]
                };
            const BUNDLE: ::schema::TyDefBundle = ::schema::TyDefBundle {
                def: ::schema::TyDef {
                    ty: <Self as ::schema::HasSchema>::TY,
                    body: #body,
                },
                child_defs: || &[#child_field_bundles],
            };
        }
    };
    proc_macro::TokenStream::from(expanded)
}
// Add a bound `T: HasSchema` to every type parameter T.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(::schema::HasSchema));
        }
    }
    generics
}
fn fields_to_body_and_children(fields: Fields) -> (TokenStream, TokenStream) {
    let struct_fields = match fields {
        Fields::Named(fields) => fields.named,
        Fields::Unnamed(fields) => fields.unnamed,
        Fields::Unit => Punctuated::new(),
    };
    for f in &struct_fields {
        check_no_serde(&f.attrs);
    }
    let child_field_bundles = make_child_field_bundles(&struct_fields);
    let body = make_body(&struct_fields);
    (body, child_field_bundles)
}
type FieldList = syn::punctuated::Punctuated<syn::Field, syn::token::Comma>;
/// Make the "Field{name: ..., ty: ...}, ..., Field{name: ..., ty: ty}" syntax.
fn make_body(fields: &FieldList) -> TokenStream {
    let descrs = fields.iter().enumerate().map(|(i, field)| {
        let name = match field.ident.as_ref() {
            None => i.to_string(),
            Some(ident) => ident.to_string(),
        };
        let ty = &field.ty;
        let ty_call = quote_spanned!(ty.span()=> <#ty as ::schema::HasSchema>::TY);
        quote!(::schema::Field{name: #name, ty: #ty_call})
    });
    quote!(&[#(#descrs),*])
}
/// Make the "&ty::BUNDLE, ..., &ty::BUNDLE" syntax.
fn make_child_field_bundles(fields: &FieldList) -> TokenStream {
    let child_bundles = fields.iter().map(|field| {
        let ty = &field.ty;
        quote_spanned!(ty.span()=> &<#ty as ::schema::HasSchema>::BUNDLE)
    });
    quote!(#(#child_bundles,)*)
}
fn is_opaque(attrs: &[Attribute]) -> bool {
    let opaque_ident: Ident = parse_quote!(schema_opaque);
    for a in attrs {
        if a.path.is_ident(&opaque_ident) {
            return true;
        }
    }
    false
}
fn check_no_serde(attrs: &[Attribute]) {
    let serde_ident: Ident = parse_quote!(serde);
    let bound_ident: Ident = parse_quote!(bound);
    let transparent_ident: Ident = parse_quote!(transparent);
    for a in attrs {
        if a.path.is_ident(&serde_ident) {
            if let Ok(Meta::List(meta_list)) = a.parse_meta() {
                if meta_list.nested.len() == 1 {
                    match meta_list.nested[0] {
                        // Match #[serde(bound(...))]
                        // Serde bounds don't change wire format.
                        NestedMeta::Meta(Meta::List(ref inner))
                            if inner.path.is_ident(&bound_ident) =>
                        {
                            continue;
                        }
                        // Match #[serde(transparent)]
                        // Transparent doesn't change bincode wire format.
                        NestedMeta::Meta(Meta::Path(ref path))
                            if path.is_ident(&transparent_ident) =>
                        {
                            continue;
                        }
                        _ => {}
                    }
                }
            }
            abort!(
                a.span(),
                "#[serde] attributes other than #[serde(bound(...))] not yet \
                 supported by HasSchema"
            );
        }
    }
}
