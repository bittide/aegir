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

use proc_macro2::{Punct, Spacing, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt};
use syn::parse::Parse;

pub fn link(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let spec = syn::parse_macro_input!(tokens as LinkSpec);

    let src_instance = spec.src_instance;
    let src_port = spec.src_port.label();
    let dst_instance = spec.dst_instance;
    let dst_port = spec.dst_port.label();
    let app_spec = &spec.app_spec;
    let framing_lead = spec.framing_lead;

    let tokens = quote! { {
        use platform::NodeSpec;

        let conn__ = platform::Connection::new(
            #app_spec.get_node(#src_instance)
                .borrow()
                .get_port(&#src_port)
                .unwrap_or_else(|| panic!("Missing source port '{}' in node '{}'",
                                          #src_port,
                                          #app_spec.get_node(#src_instance).borrow().name())),
            #app_spec.get_node(#dst_instance)
                .borrow()
                .get_port(&#dst_port)
                .unwrap_or_else(|| panic!("Missing destination port '{}' in node '{}'",
                                          #dst_port,
                                          #app_spec.get_node(#dst_instance).borrow().name())),
        );

        #app_spec.link_simplex_framing(
            #src_instance,
            #dst_instance,
            conn__,
            // TODO(cascaval): fixup the PortProperties in the connection,
            // and then lookup the framing lead in Connection. The
            // PortProperties were set at a point when the framing lead was
            // unknown.
            #framing_lead,
        )
    }};

    tokens.into()
}

pub struct ArrayPort {
    name: syn::Ident,
    index: syn::Expr,
}

impl Parse for ArrayPort {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        let name = input.parse()?;
        let _bracket = syn::bracketed!(content in input);
        let index = content.parse()?;
        Ok(ArrayPort { name, index })
    }
}

impl ToTokens for ArrayPort {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.name.to_tokens(tokens);
        tokens.append(Punct::new('[', Spacing::Joint));
        self.index.to_tokens(tokens);
        tokens.append(Punct::new(']', Spacing::Joint));
    }
}

impl Parse for Port {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(if input.peek2(syn::token::Bracket) {
            Self::Array(input.parse()?)
        } else {
            Self::Named(input.parse()?)
        })
    }
}

impl Port {
    fn label(&self) -> proc_macro2::TokenStream {
        match self {
            Port::Array(ArrayPort { name, index }) => {
                quote! { platform::PortLabel::from((stringify!(#name), #index)) }
            }
            Port::Named(name) => quote! { platform::PortLabel::from(stringify!(#name)) },
        }
    }
}

enum Port {
    Array(ArrayPort),
    Named(syn::Ident),
}

struct LinkSpec {
    src_instance: syn::Expr,
    src_port: Port,
    dst_instance: syn::Expr,
    dst_port: Port,
    app_spec: syn::Ident,
    framing_lead: proc_macro2::TokenStream,
}

impl Parse for LinkSpec {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let src_instance = input.parse()?;
        let src_port = input.parse()?;
        let _arrow: syn::Token![->] = input.parse()?;
        let dst_instance = input.parse()?;
        let dst_port = input.parse()?;
        let framing_lead = if input.peek(syn::Token![as]) {
            let _as: syn::Token![as] = input.parse()?;
            let lead: syn::Ident = input.parse()?;
            if lead != "lead" {
                return Err(syn::Error::new(lead.span(), "expected 'lead''"));
            }
            quote!(platform::FramingLead::Dst)
        } else {
            quote!(platform::FramingLead::Src)
        };
        let _in: syn::Token![in] = input.parse()?;
        let app_spec = input.parse()?;

        Ok(Self {
            src_instance,
            src_port,
            dst_instance,
            dst_port,
            app_spec,
            framing_lead,
        })
    }
}
