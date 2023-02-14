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

use proc_macro2::TokenStream;
use quote::quote;
use std::fmt;
use syn::parse::Parse;

/**
 * Given a type, `T`, if `T = Option<U>`, return `U` else `None`.
 */
pub fn get_option_inner_type(ty: &syn::Type) -> Option<&syn::Type> {
    match &ty {
        syn::Type::Path(type_path) => {
            let segs = &type_path.path.segments;
            if segs.len() == 1 && segs[0].ident == "Option" {
                match &segs[0].arguments {
                    syn::PathArguments::AngleBracketed(angle_bracketed) => {
                        if angle_bracketed.args.len() == 1 {
                            match &angle_bracketed.args[0] {
                                syn::GenericArgument::Type(ty) => Some(ty),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            } else {
                None
            }
        }
        _ => None,
    }
}
pub struct IdentType {
    name: syn::Ident,
    _colon: syn::Token![:],
    ty: syn::Type,
}

impl fmt::Debug for IdentType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use quote::ToTokens;
        f.write_fmt(format_args!(
            "{}: {}",
            self.name.to_token_stream().to_string(),
            self.ty.to_token_stream().to_string(),
        ))?;
        Ok(())
    }
}

impl IdentType {
    pub fn get_type(&self) -> &syn::Type {
        &self.ty
    }

    pub fn get_inner_type(&self) -> &syn::Type {
        if let syn::Type::Array(t) = &self.ty {
            &*t.elem
        } else {
            &self.ty
        }
    }

    pub fn get_name(&self) -> &syn::Ident {
        &self.name
    }

    pub fn get_length(&self) -> syn::Result<syn::Expr> {
        if let syn::Type::Array(t) = &self.ty {
            Ok(t.len.clone())
        } else {
            syn::parse_str("1")
        }
    }

    /// create a local variable with the self.name and initialize it from
    /// input_bits[input_pos__].
    ///
    /// Assumes that input_pos__ has been declared and points to the start element in input_bits.
    /// Increment the position based on this variable lenght.
    pub fn get_deserializer(&self) -> syn::Result<TokenStream> {
        let len = self.get_length()?;
        let name = self.get_name();
        let ty = self.get_type();
        let ts = if let syn::Type::Array(_) = self.get_type() {
            let inner_type = self.get_inner_type();
            if let Some(opt_type) = get_option_inner_type(inner_type) {
                quote! {
                    let #name = input_bits[input_pos__..(input_pos__ + #len)]
                        .iter()
                        .map(|inp__| {
                            inp__.map(|bits| <#opt_type>::unpack(bits))
                        }).
                        collect::<std::vec::Vec<#inner_type>>();
                    input_pos__ += #len;
                }
            } else {
                quote! {
                    let #name = input_bits[input_pos__..(input_pos__ + #len)]
                        .iter()
                        .map(|inp__| {
                            inp__.map(|bits| <#inner_type>::unpack(bits))
                                 .unwrap_or(<#inner_type>::default())
                        }).
                        collect::<std::vec::Vec<#inner_type>>();
                    input_pos__ += #len;
                }
            }
        } else {
            if get_option_inner_type(ty).is_some() {
                let ty = get_option_inner_type(ty);
                quote! {
                    let #name = input_bits[input_pos__].map(|bits| <#ty>::unpack(bits));
                    input_pos__ += 1;
                }
            } else {
                quote! {
                    let #name = if let Some(bits) = input_bits[input_pos__] {
                        <#ty>::unpack(bits)
                    } else {
                        log::info!("Skipping because input {} is not present", stringify!(#name));
                        return;
                    };
                    input_pos__ += 1;
                }
            }
        };
        Ok(ts)
    }

    /// serialize the output variable list into output_bits[output_pos__].
    ///
    /// Assumes that output_pos__ has been declared and points to the start element in output_bits.
    /// Increment the position based on this variable length.
    pub fn get_serializer(&self) -> syn::Result<TokenStream> {
        let len = self.get_length()?;
        let name = self.get_name();
        let ty = self.get_inner_type();
        let ts = if get_option_inner_type(ty).is_some() {
            if let syn::Type::Array(_) = &self.ty {
                quote! {
                    for idx__ in 0..#len {
                        if let Some(output_val) = & #name[idx__] {
                            output_val.pack_to(&mut output_bits[output_pos__ + idx__].data);
                            output_bits[output_pos__ + idx__].valid = true;
                        } else {
                            output_bits[output_pos__ + idx__].valid = false;
                        }
                    }
                    output_pos__ += #len;
                }
            } else {
                quote! {
                    if let Some(output_val) = & #name {
                        output_val.pack_to(&mut output_bits[output_pos__].data);
                        output_bits[output_pos__].valid = true;
                    } else {
                        output_bits[output_pos__].valid = false;
                    }
                    output_pos__ += 1;
                }
            }
        } else {
            if let syn::Type::Array(_) = &self.ty {
                quote! {
                    for idx__ in 0..#len {
                        #name[idx__].pack_to(&mut output_bits[output_pos__ + idx__].data);
                        output_bits[output_pos__ + idx__].valid = true;
                    }
                    output_pos__ += #len;
                }
            } else {
                quote! {
                    #name.pack_to(&mut output_bits[output_pos__].data);
                    output_bits[output_pos__].valid = true;
                    output_pos__ += 1;
                }
            }
        };
        Ok(ts)
    }

    /// return a declaration for the variable.
    ///
    /// this is typically used for output variables (input variables are
    /// declared as part of the deserialization). However, for outputs, we
    /// need to declare the variables ahead of invoking the body, thus
    /// decoupled from serialization.
    pub fn get_decl(&self) -> syn::Result<TokenStream> {
        let name = self.get_name();
        let ty = self.get_type();
        let ts = if let Some(inner_type) = get_option_inner_type(ty) {
            quote! {
                #[allow(unused_assignments)]
                let mut #name: std::option::Option::<#inner_type> = std::option::Option::None;
            }
        } else {
            quote! {
                let mut #name: #ty;
            }
        };
        Ok(ts)
    }
}

impl Parse for IdentType {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            name: input.parse()?,
            _colon: input.parse()?,
            ty: input.parse()?,
        })
    }
}

pub struct VarList(syn::punctuated::Punctuated<IdentType, syn::Token![,]>);

impl fmt::Debug for VarList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self
            .0
            .iter()
            .map(|ident_type| format!("{:?}", ident_type))
            .collect::<Vec<String>>()
            .join(", ");
        f.write_str(&s)?;
        Ok(())
    }
}

impl VarList {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    fn iter(&self) -> syn::punctuated::Iter<'_, IdentType> {
        self.0.iter()
    }

    /// turn a list of variables (input/output ports) into a list of pairs:
    /// (PortLabels, PortProperties) that are used to represent ports in topologies.
    fn to_ports(&self, dir: TokenStream) -> syn::Result<Vec<TokenStream>> {
        let mut port_descriptors = Vec::new();
        for field in self.iter() {
            let name = field.get_name();
            if let syn::Type::Array(t) = field.get_type() {
                let len = field.get_length()?;
                let ty = get_option_inner_type(&*t.elem).unwrap_or_else(|| &*t.elem);
                port_descriptors.push(quote! { (
                    platform::PortLabel::from((stringify!(#name), #len)),
                    platform::PortProperties {
                        direction: #dir,
                        frame_size: platform::FrameSize::Computed(platform::RttiType::new::<#ty>()),
                        ..platform::PortProperties::default()
                    },
                )});
            } else {
                let ty =
                    get_option_inner_type(field.get_type()).unwrap_or_else(|| field.get_type());
                port_descriptors.push(quote! {(
                    platform::PortLabel::from(stringify!(#name)),
                    platform::PortProperties {
                        direction: #dir,
                        frame_size: platform::FrameSize::Computed(platform::RttiType::new::<#ty>()),
                        ..platform::PortProperties::default()
                    },
                )});
            }
        }
        Ok(port_descriptors)
    }

    fn port_lengths(&self) -> syn::Result<Vec<TokenStream>> {
        Ok(self
            .iter()
            .map(|field| {
                let len = field.get_length().unwrap();
                quote! { #len }
            })
            .collect())
    }

    /// the list that declares and initializes all inputs.
    fn get_deserializers(&self) -> syn::Result<Vec<TokenStream>> {
        let mut deserializers = Vec::new();
        for field in self.iter() {
            deserializers.push(field.get_deserializer()?);
        }
        Ok(deserializers)
    }

    /// the list of output variable declarations.
    fn get_decls(&self) -> syn::Result<Vec<TokenStream>> {
        let mut decls = Vec::new();
        for field in self.iter() {
            decls.push(field.get_decl()?);
        }
        Ok(decls)
    }

    /// the list of output variable serializations.
    fn get_serializers(&self) -> syn::Result<Vec<TokenStream>> {
        let mut serializers = Vec::new();
        for field in self.iter() {
            serializers.push(field.get_serializer()?);
        }
        Ok(serializers)
    }

    /// a pair of (state_deserialize, state_serialize) statements.
    fn get_state_serdes(
        &self,
        action_name: &TokenStream,
    ) -> syn::Result<(TokenStream, TokenStream)> {
        let (state_types, state_names): (Vec<&syn::Type>, Vec<&syn::Ident>) =
            self.iter().map(|f| (f.get_type(), f.get_name())).unzip();

        if self.is_empty() {
            Ok((quote! {}, quote! {}))
        } else {
            Ok((
                quote! {
                    let state_bits = &mut state_bits_opt
                        .unwrap_or_else(|| panic!("No state present in {}", stringify!(#action_name)));
                    let (#(mut #state_names,)*) = <(#(#state_types,)*)>::unpack(state_bits.as_bitslice());
                },
                quote! {
                    (#(#state_names,)*).pack_to(state_bits);
                },
            ))
        }
    }
}

impl Parse for VarList {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(VarList(syn::punctuated::Punctuated::<
            IdentType,
            syn::Token![,],
        >::parse_terminated(input)?))
    }
}

/// type signature for Action
pub struct ActionType {
    state_vars: super::util::VarList,
    input_vars: super::util::VarList,
    output_vars: super::util::VarList,
}

impl Parse for ActionType {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let state_content;
        let input_content;
        let output_content;
        let _state_parens = syn::parenthesized!(state_content in input);
        let state_vars = state_content.parse()?;
        let _input_parens = syn::parenthesized!(input_content in input);
        let input_vars = input_content.parse()?;
        let _arrow: syn::Token![->] = input.parse()?;
        let _output_parens = syn::parenthesized!(output_content in input);
        let output_vars = output_content.parse()?;
        Ok(Self {
            state_vars,
            input_vars,
            output_vars,
        })
    }
}

impl ActionType {
    /// Generates a function prototype for an action
    pub fn to_fn(
        &self,
        action_name: &syn::Ident,
        action_body: &syn::Block,
    ) -> syn::Result<TokenStream> {
        let name = quote! { stringify!{#action_name} };
        let body = self.get_body(&name, action_body)?;
        let tokens = quote! {
            pub fn #action_name (
                state_bits_opt: platform::LoopbackRef,
                input_bits: &[platform::InputFrameRef],
                output_bits: &mut [platform::OutputFrameRef],
                sys: &dyn platform::SystemContext,
            ) #body
        };
        Ok(tokens)
    }

    /// Generates a closure for the action
    pub fn to_lambda(
        &self,
        action_name: &TokenStream,
        action_body: &syn::Block,
    ) -> syn::Result<TokenStream> {
        let body = self.get_body(action_name, action_body)?;
        let tokens = quote! {
            | state_bits_opt: platform::LoopbackRef,
              input_bits: &[platform::InputFrameRef],
              output_bits: &mut [platform::OutputFrameRef],
              sys: &dyn platform::SystemContext,
            | #body
        };
        Ok(tokens)
    }

    /// enumerate all the ports and return two pairs of lists with port descriptors
    pub fn get_ports(&self) -> syn::Result<(Vec<TokenStream>, Vec<TokenStream>)> {
        let input_ports = self
            .input_vars
            .to_ports(quote!(platform::Direction::Incoming))?;
        let output_ports = self
            .output_vars
            .to_ports(quote!(platform::Direction::Outgoing))?;
        Ok((input_ports, output_ports))
    }

    /// Generates the body of the action
    ///
    /// action_name is a TokenStream to handle both identifiers and
    /// expressions that evaluate to strings.
    fn get_body(
        &self,
        action_name: &TokenStream,
        action_body: &syn::Block,
    ) -> syn::Result<TokenStream> {
        // use macro expansion to compute the size of the ports, this allows
        // us to use constant expressions for array sizes.
        let input_ports_lengths = self.input_vars.port_lengths()?;
        let output_ports_lengths = self.output_vars.port_lengths()?;

        // the serialization/deserialization; these return token streams
        // that can be used directly in the expansion.
        let input_deserializers = self.input_vars.get_deserializers()?;
        let output_serializers = self.output_vars.get_serializers()?;
        let output_declarations = self.output_vars.get_decls()?;

        let (state_deserialize, state_serialize) = self.state_vars.get_state_serdes(action_name)?;

        let tokens = quote! {
            {
                use bits::Bits;

                let input_ports_count__: usize = std::vec![
                    #(
                        #input_ports_lengths
                    ),*
                ].iter().sum();
                let output_ports_count__: usize = std::vec![
                    #(
                        #output_ports_lengths
                    ),*
                ].iter().sum();
                /*
                If the name is an expression, we can not make a lambda into
                a fn, which is what we need to pass to a node. Example
                error:

                closures can only be coerced to `fn` types if they do not capture any variables
                action!(name.as_str() in app_spec (counter: u64) () -> (output: u64) {
                        ^^^^ `name` captured here

                Therefore, we print the file and line number where the action has been defined.
                */
                assert!(input_bits.len() == input_ports_count__,
                        "Found {} inputs, expected {} in {}:{}",
                        input_bits.len(), input_ports_count__, std::file!(), std::line!());
                assert!(output_bits.len() == output_ports_count__,
                        "Found {} outputs, expected {} in {}:{}",
                        output_bits.len(), output_ports_count__, std::file!(), std::line!());
                // initialize the counter for inputs
                let mut input_pos__ = 0;
                #(
                    #input_deserializers
                )*

                #state_deserialize

                #(
                    #output_declarations
                )*

                #action_body

                #state_serialize

                // initialize the counter for outputs
                let mut output_pos__ = 0;
                #(
                    #output_serializers
                )*
            }
        };
        Ok(tokens)
    }
}
