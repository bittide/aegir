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

#![allow(dead_code)]

#[cfg(test)]
mod tests {
    use schema::*;
    use serde::Serialize;
    use std::collections::HashSet;

    fn transitive_def_tys<T: HasSchema>() -> HashSet<Ty> {
        schema::schema::<T>()
            .defs
            .iter()
            .map(|td| td.ty.clone())
            .collect()
    }

    fn make_tys(names: &[Ty]) -> HashSet<Ty> {
        names.iter().cloned().collect()
    }

    #[derive(HasSchema)]
    struct EmptyStruct {}

    #[test]
    fn empty_struct() {
        assert_eq!(
            Ty {
                name: "schema_test::tests::EmptyStruct",
                args: &[]
            },
            EmptyStruct::TY
        );
        assert_eq!(Body::Struct(&[]), EmptyStruct::BUNDLE.def.body);
        assert_eq!(
            make_tys(&[Ty {
                name: "schema_test::tests::EmptyStruct",
                args: &[],
            }]),
            transitive_def_tys::<EmptyStruct>()
        );
    }

    #[derive(HasSchema)]
    struct StructWithFields {
        foo: EmptyStruct,
        bar: EmptyStruct,
    }

    #[test]
    fn struct_with_fields() {
        assert_eq!(
            Ty {
                name: "schema_test::tests::StructWithFields",
                args: &[]
            },
            StructWithFields::TY
        );
        assert_eq!(
            Body::Struct(&[
                Field {
                    name: "foo",
                    ty: Ty {
                        name: "schema_test::tests::EmptyStruct",
                        args: &[],
                    },
                },
                Field {
                    name: "bar",
                    ty: Ty {
                        name: "schema_test::tests::EmptyStruct",
                        args: &[]
                    },
                },
            ]),
            StructWithFields::BUNDLE.def.body
        );
        assert_eq!(
            make_tys(&[
                Ty {
                    name: "schema_test::tests::EmptyStruct",
                    args: &[],
                },
                Ty {
                    name: "schema_test::tests::StructWithFields",
                    args: &[],
                },
            ]),
            transitive_def_tys::<StructWithFields>()
        );
    }

    #[derive(HasSchema)]
    struct UnnamedFields(EmptyStruct, EmptyStruct);

    #[test]
    fn unnamed_fields() {
        assert_eq!(
            Ty {
                name: "schema_test::tests::UnnamedFields",
                args: &[]
            },
            UnnamedFields::TY
        );
        assert_eq!(
            Body::Struct(
                &[
                    Field {
                        name: "0",
                        ty: Ty {
                            name: "schema_test::tests::EmptyStruct",
                            args: &[],
                        },
                    },
                    Field {
                        name: "1",
                        ty: Ty {
                            name: "schema_test::tests::EmptyStruct",
                            args: &[]
                        },
                    },
                ][..]
            ),
            UnnamedFields::BUNDLE.def.body
        );
        assert_eq!(
            make_tys(&[
                Ty {
                    name: "schema_test::tests::EmptyStruct",
                    args: &[],
                },
                Ty {
                    name: "schema_test::tests::UnnamedFields",
                    args: &[],
                },
            ]),
            transitive_def_tys::<UnnamedFields>()
        );
    }

    /// Make sure that the deriving mechanism works even if nothing is in scope and
    /// there's a conflicting 'schema' module.
    mod hygiene_test {
        mod schema {}

        #[derive(::schema::HasSchema)]
        struct GenericStruct<T> {
            x: super::EmptyStruct,
            y: T,
        }
    }

    #[derive(HasSchema, Serialize)]
    enum SomeEnum {
        Foo,
        Bar(u32),
        Baz {
            x: u32,
            #[serde(bound(serialize = ""))]
            y: u8,
        },
    }

    #[test]
    fn some_enum() {
        assert_eq!(
            Ty {
                name: "schema_test::tests::SomeEnum",
                args: &[]
            },
            SomeEnum::TY
        );
        assert_eq!(
            Body::Enum(&[
                Variant {
                    name: "Foo",
                    fields: &[],
                },
                Variant {
                    name: "Bar",
                    fields: &[Field {
                        name: "0",
                        ty: Ty {
                            name: "u32",
                            args: &[],
                        },
                    },],
                },
                Variant {
                    name: "Baz",
                    fields: &[
                        Field {
                            name: "x",
                            ty: Ty {
                                name: "u32",
                                args: &[],
                            },
                        },
                        Field {
                            name: "y",
                            ty: Ty {
                                name: "u8",
                                args: &[],
                            },
                        },
                    ],
                },
            ]),
            SomeEnum::BUNDLE.def.body
        );
        assert_eq!(
            make_tys(&[
                Ty {
                    name: "u32",
                    args: &[],
                },
                Ty {
                    name: "u8",
                    args: &[],
                },
                Ty {
                    name: "schema_test::tests::SomeEnum",
                    args: &[],
                },
            ]),
            transitive_def_tys::<SomeEnum>()
        );
    }

    struct NoHasSchema {}

    #[derive(HasSchema)]
    #[schema_opaque]
    struct OpaqueStruct<T> {
        x: Vec<T>,
        y: NoHasSchema,
    }
    #[test]
    fn opaque_struct() {
        assert_eq!(
            Ty {
                name: "schema_test::tests::OpaqueStruct",
                args: &[&Ty {
                    name: "schema_test::tests::EmptyStruct",
                    args: &[]
                }],
            },
            OpaqueStruct::<EmptyStruct>::TY
        );
        assert_eq!(
            Body::Opaque(0),
            OpaqueStruct::<EmptyStruct>::BUNDLE.def.body
        );
        assert_eq!(
            make_tys(&[Ty {
                name: "schema_test::tests::OpaqueStruct",
                args: &[&Ty {
                    name: "schema_test::tests::EmptyStruct",
                    args: &[]
                }],
            },]),
            transitive_def_tys::<OpaqueStruct<EmptyStruct>>()
        );
    }

    #[derive(HasSchema)]
    struct RecursiveStruct {
        left: Box<RecursiveStruct>,
        right: Box<RecursiveStruct>,
    }

    // #[test]
    fn recursive_struct() {
        assert_eq!(
            Ty {
                name: "schema_test::tests::RecursiveStruct",
                args: &[]
            },
            RecursiveStruct::TY
        );
        assert_eq!(
            Body::Struct(
                &[
                    Field {
                        name: "left",
                        ty: Ty {
                            name: "schema_test::tests::RecursiveStruct",
                            args: &[],
                        },
                    },
                    Field {
                        name: "right",
                        ty: Ty {
                            name: "schema_test::tests::RecursiveStruct",
                            args: &[]
                        },
                    },
                ][..]
            ),
            RecursiveStruct::BUNDLE.def.body
        );
        assert_eq!(
            make_tys(&[Ty {
                name: "schema_test::tests::RecursiveStruct",
                args: &[]
            },]),
            transitive_def_tys::<RecursiveStruct>()
        );
    }
}

// Test with:
//   RUSTFLAGS='--cfg compile_failures' cargo test
#[cfg(compile_failures)]
mod compile_failures {
    use schema::HasSchema;
    use serde::Serialize;

    // Only works on structs
    #[derive(HasSchema)]
    enum Foo {
        Bar,
    }

    struct NoHasSchema {}

    // x doesn't implement HasSchema.
    #[derive(HasSchema)]
    struct Bar {
        x: NoHasSchema,
    }

    // Unsupported #[serde(...)] tag.
    #[derive(HasSchema, Serialize)]
    struct Quux {
        #[serde(skip)]
        x: u32,
        y: u32,
    }
}
