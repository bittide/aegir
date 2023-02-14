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

use super::util::ActionType;
use proc_macro::TokenStream;
use syn::parse::Parse;

/// Syntax:
///
/// ```text
/// action_fn!(name (states*) (inputs*) -> (outputs*) { body })
/// ```
///
/// generates a function with `platform::Action` type signature within the
/// calling context.
///
pub fn action_fn(tokens: TokenStream) -> TokenStream {
    let act = syn::parse_macro_input!(tokens as ActionFnSpec);
    act.action_type
        .to_fn(&act.name, &act.body)
        .unwrap_or_else(|err| err.into_compile_error().into())
        .into()
}

struct ActionFnSpec {
    name: syn::Ident,
    action_type: ActionType,
    body: syn::Block,
}

impl Parse for ActionFnSpec {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let name = input.parse()?;
        let action_type = input.parse()?;
        let body = input.parse()?;
        Ok(Self {
            name,
            action_type,
            body,
        })
    }
}
