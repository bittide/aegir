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

//! Syntax:
//!
//! ```text
//! action!(name in topology (states*) (inputs*) -> (outputs*) { init-block } { body })
//! action!(name in topology (states*) (inputs*) -> (outputs*) { init-block } action_fn_name)
//! ```
//!
//! generates the following code:
//!
//! ```text
//!
//! topology.add_node(platform::Service::new(
//!   "name",             // node name
//!   action_fn_name,     // action function name or lambda representing the function
//!   None,               // initial state
//!   FrequencyFactor(1), // repeat factor
//!   1,                  // CyclesPerMetacycle
//! ))
//! ```

use super::util::ActionType;
use quote::quote;
use syn::parse::Parse;

// TODO(cascaval): consider how to pass FrequencyFactor and
// CyclesPerMetacycle as parameters to the macro.

pub fn action(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let spec = syn::parse_macro_input!(tokens as ActionSpec);
    spec.expand()
        .unwrap_or_else(|err| err.into_compile_error().into())
}

impl ActionSpec {
    fn expand(&self) -> syn::Result<proc_macro::TokenStream> {
        let app_spec = &self.topology;
        let node_name = &self.name;
        let (input_ports, output_ports) = &self.action_type.get_ports()?;

        let one = syn::Expr::Verbatim(quote!(1));
        let freq = self.freq.as_ref().unwrap_or(&one);
        let action_spec = if let Some(action_fn) = &self.action_fn {
            quote! { #action_fn }
        } else {
            let action_name = quote! { #node_name };
            self.action_type
                .to_lambda(&action_name, &self.body.as_ref().unwrap())?
        };
        let set_node_state = if self.init_block.stmts.len() == 0 {
            quote!()
        } else {
            let init_block = &self.init_block;
            quote! {
                #[allow(unused_braces)]
                #app_spec.set_node_state(node__, #init_block);
            }
        };
        let tokens = quote! { {
            use platform::NodeSpec;
            let mut svc__ = platform::Service::new(
                #node_name,
                #action_spec,
                None,                // initial state
                platform::FrequencyFactor(#freq),  // repeat factor
            );
            svc__.set_ports_properties(&[
                #(
                    #input_ports,
                )*
                #(
                    #output_ports,
                )*
            ]);
            let node__ = #app_spec.add_node(svc__);
            #set_node_state;
            node__
        }};

        Ok(tokens.into())
    }
}

struct ActionSpec {
    name: syn::Expr,
    freq: Option<syn::Expr>,
    topology: syn::Ident,
    action_type: ActionType,
    action_fn: Option<syn::Path>,
    init_block: syn::Block,
    body: Option<syn::Block>,
}

// TODO(pouyad) Ideally the init block wouldn't need to spell out serialization
// of the state fields. Preferably one could write for instance { some_state =
// state_value } where the serialization of state_value is automated.

// TODO(pouyad) Improve the error reporting, e.g., missing initializer or action
// block?
impl Parse for ActionSpec {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        let freq = if input.peek(syn::Token![@]) {
            let _at: syn::Token![@] = input.parse()?;
            Some(input.parse()?)
        } else {
            None
        };
        let _in: syn::Token![in] = input.parse()?;
        let topology = input.parse()?;
        let action_type = input.parse()?;
        let mut body = None;
        let mut action_fn = None;
        let init_block = input.parse()?;
        if input.peek(syn::token::Brace) {
            body = Some(input.parse()?);
        } else {
            action_fn = Some(input.parse()?)
        }

        Ok(Self {
            name,
            freq,
            topology,
            action_type,
            action_fn,
            init_block,
            body,
        })
    }
}
