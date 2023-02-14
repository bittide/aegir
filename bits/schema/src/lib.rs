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

//! Serialization Schemas for types.
//!
//! The fastest serialization in compiled languages is typically direct binary
//! serialization, such as serde::bincode in Rust. However, these formats lead
//! to difficult-to-debug failures if the serializer and deserializer are using
//! different formats. This 'schema' library provides the answer: it produces
//! a schema which can be checked for compatibility, with good error messages,
//! before using the fast binary serialization format. This strategy is similar
//! in style, but not in details, to Apache Avro format:
//! <https://avro.apache.org>
//!
//! The centerpiece of this library is a `HasSchema` type trait. To use
//! binary-plus-schema serialization on your type, derive the
//! `Serialize` and/or `Deserialize` traits (from `serde`) as well as the
//! `HasSchema` trait.
//!
//! Then you can serialize your type `Foo` using `bincode`, and also produce a
//! schema that describes the format used by `bincode`:
//!
//! ```
//! use serde::Serialize;
//! use schema::HasSchema;
//! use bincode;
//!
//! #[derive(Serialize, HasSchema)]
//! struct Foo {
//!   x: u32,
//!   y: u8,
//! }
//!
//! fn serialize_foo(f: &Foo) -> (Vec<u8>, schema::Schema) {
//!   (bincode::serialize(f).unwrap(), schema::schema::<Foo>())
//! }
//! ```
//!
//! The receiver should verify compatibility with the `Schema` before trying to
//! deserialize the bytes.
//!
//! # Endianness
//!
//! Schemas do *not* specify endianness on the wire. `bincode` allows the user
//! to pick a global endianness for all fields. The user should make sure to
//! use the same endianness for `bincode` and whatever library is used on the
//! other side.
//!
//! # Schema format
//!
//! Our schemas describe how a type is serialized by `bincode`. They express
//! the following formats:
//!
//!  * Primitive types, which occupy a fixed number of bytes on the wire.
//!  * Types with a `bits::Bits` instance, which always occupy 8 bytes on
//!    the wire. Such types know their true bit width (<=64), so that the
//!    receiver can check that its bit width matches the sender's.
//!  * Fixed-size arrays. These are encoded on the wire as the N-way
//!    concatenation of the underlying type.
//!  * Variable-size arrays. These are encoded on the wire as an 8-byte
//!    length, followed by the N-way concatenation of the underlying type.
//!  * Structs. These are encoded as the concatenation of the struct's fields.
//!
//! Schemas provide enough information to verify compatibility of the
//! following properties:
//!  * Compatibility of wire sizes of all types.
//!  * Compatibility of bit widths of Bits instances.
//!  * Type names of all types, transitively: traversing into struct
//!    fields and array elements.
//!  * Field names and field order of structs.
//!
//! # Correspondence between `HasSchema` and `serde`/`bincode`
//!
//! The `schema` library is designed to be used with the `serde` and `bincode`
//! libraries, in the sense that the schemas produced by `HasSchema`
//! correspond to the serialization format used by `bincode`. However, this
//! correspondence can be broken: there is nothing to stop you from defining
//! as `HasSchema` impl with completely different behavior from the `Serialize`
//! impl of the same type. This would lead to a buggy schema.
//!
//! To avoid such bugs, you should treat manual implementations of `Serialize`
//! and `HasSchema` as likely sources of bugs, and avoid them if possible.
//! Instead, use `#[derive(HasSchema, Serialize)]` or `bits::serde_as_bits` if
//! possible, which are designed to keep the implementations in sync.
//!
//! # Static types
//!
//! The types used in schemas have static lifetimes, because they are intended
//! to be global constants. Indeed, the entire schema library does almost no
//! dynamic memory allocations: there are just three, in the Depth First Search
//! inside `schema::schema`.
pub use schema_derive::*;
use serde::Serialize;
use std::collections::HashSet;
use std::hash::Hash;
/// A type definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct TyDef {
    /// Name of this type.
    pub ty: Ty,
    /// Fields of this type, or None if it's an opaque type.
    ///
    /// Opaque types are *not* checked for match by the schema.
    pub body: Body,
}
/// A type definition, plus pointers to child type definitions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TyDefBundle {
    pub def: TyDef,
    /// All type definitions needed to transitivitely check compatibility with
    /// this schema.
    pub child_defs: fn() -> &'static [&'static TyDefBundle],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Body {
    /// We don't specify how this is serialized. Schema checking will fail when
    /// we encounter a value of this type.
    ///
    /// usize field is useless; it just works around b/144129087.
    Opaque(usize),
    /// Serialized as a primitive type with the specified number of bytes.
    Primitive(usize),
    /// Something with a Bits instance with specified number of bits.
    ///
    /// Serialized as a u64.
    Bits(u32),
    /// Something serialized in (arraylen: u64, payload: [ty; arraylen]) format.
    Array(Ty),
    /// Something serialized in fixed-size-array format.
    ArrayN(u32, Ty),
    /// Serialized as a struct with the specified fields.
    Struct(&'static [Field]),
    /// Single-byte 0 for None.
    /// Single-byte 1, followed by payload, for Some.
    Option(Ty),
    /// Serialized enum with the specified option.
    ///
    /// Wire format is `u32` tag (enum options listed in 0,1,2,... tag order)
    /// follow by concatenation of the fields of the chosen option.
    Enum(&'static [Variant]),
}
/// A variant of an enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct Variant {
    pub name: &'static str,
    pub fields: &'static [Field],
}
/// A field of a struct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct Field {
    /// The field's name. For anonymous structs, the fields will be numbered
    /// "0", "1", etc.
    pub name: &'static str,
    /// The field's type.
    pub ty: Ty,
}
/// A type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Hash)]
pub struct Ty {
    /// Full type name, including full module path.
    pub name: &'static str,
    /// Type arguments.
    pub args: &'static [&'static Ty],
}
/// Type trait for types that have schemas.
///
/// Don't use the members of this trait directly. Instead, use
/// `schema::schema`.
pub trait HasSchema {
    /// The schema of the type, plus all its immediate children.
    ///
    /// Typically you should use schema::<T>() instead, which fetches the
    /// schema in a more useful, with all transitively referenced types.
    const BUNDLE: TyDefBundle;
    /// The type.
    ///
    /// This is duplicated from `BUNDLE.def.ty` for boring reasons around
    /// avoiding circular dependencies for recursive data types.
    const TY: Ty;
}
/// A schema describing the serialization format of a type, plus all of
/// its transitively-referenced types.
#[derive(Clone, Debug, Serialize)]
pub struct Schema {
    /// The top-level type being serialized.
    pub root: Ty,
    /// Type definitions for all transitively referenced types.
    pub defs: Vec<TyDef>,
}
/// Transitively gets all TyDefs starting at the given set of roots.
pub fn schema<T: HasSchema>() -> Schema {
    schema_impl(T::BUNDLE)
}
fn schema_impl(root: TyDefBundle) -> Schema {
    let mut queue = vec![&root];
    let mut seen = HashSet::new();
    let mut defs = Vec::new();
    while let Some(bundle) = queue.pop() {
        if !seen.insert(&bundle.def.ty) {
            continue;
        }
        defs.push(bundle.def);
        queue.extend_from_slice((bundle.child_defs)());
    }
    Schema {
        root: root.def.ty,
        defs,
    }
}
///////////////////////////////////////////////////////////////////////////////
/// Reference types forward to their underlying type
///////////////////////////////////////////////////////////////////////////////
macro_rules! impl_schema_by_forward {
    ($outer:ty, $inner:ident) => {
        impl<$inner: HasSchema + ?Sized> HasSchema for $outer {
            const TY: Ty = $inner::TY;
            const BUNDLE: TyDefBundle = $inner::BUNDLE;
        }
    };
}
impl_schema_by_forward!(&T, T);
impl_schema_by_forward!(&mut T, T);
impl_schema_by_forward!(Box<T>, T);
////////////////////////////////////////////////////////////////////////////////
// std types
////////////////////////////////////////////////////////////////////////////////
macro_rules! impl_schema {
    ($name:expr, $tapp:ty, $body:expr, $($arg:ident),*) => {
        impl <$($arg: HasSchema),*> HasSchema for $tapp {
            const TY: Ty = Ty {
                name: $name,
                args: &[$(&$arg::TY),*]
            };
            const BUNDLE: TyDefBundle = TyDefBundle {
                def: TyDef {
                    ty: Self::TY,
                    body: $body,
                },
                child_defs: || &[$(&$arg::BUNDLE),*],
            };
        }
    };
}
macro_rules! impl_array {
    ($n:literal) => {
        impl_schema!(
            std::concat!("Array", $n),
            [T; $n],
            Body::ArrayN($n, T::TY),
            T
        );
    };
}
impl_array!(0);
impl_array!(1);
impl_array!(2);
impl_array!(3);
impl_array!(4);
impl_array!(5);
impl_array!(6);
impl_array!(7);
impl_array!(8);
impl_array!(9);
impl_array!(10);
impl_array!(11);
impl_array!(12);
impl_array!(13);
impl_array!(14);
impl_array!(15);
impl_array!(16);
impl_array!(17);
impl_array!(18);
impl_array!(19);
impl_array!(20);
macro_rules! impl_primitive {
    ($t:ty) => {
        impl_schema!(
            std::stringify!($t),
            $t,
            Body::Primitive(std::mem::size_of::<$t>()),
        );
    };
}
impl_primitive!(bool);
impl_primitive!(u8);
impl_primitive!(i8);
impl_primitive!(u16);
impl_primitive!(i16);
impl_primitive!(u32);
impl_primitive!(i32);
impl_primitive!(u64);
impl_primitive!(i64);
impl_primitive!(u128);
impl_primitive!(i128);
impl_primitive!(usize);
impl_primitive!(isize);
impl_schema!("Array", [T], Body::Array(T::TY), T);
impl_schema!("Array", std::vec::Vec<T>, Body::Array(T::TY), T);
impl_schema!(
    "Array",
    std::collections::VecDeque<T>,
    Body::Array(T::TY),
    T
);
impl_schema!("()", (), Body::Struct(&[]),);
impl_schema!("Option", std::option::Option<T>, Body::Option(T::TY), T);
impl_schema!("Result", std::result::Result<T, U>,
             Body::Enum(&[
                 Variant{name: "Ok", fields: &[Field{name: "0", ty: T::TY}]},
                 Variant{name: "Err", fields: &[Field{name: "0", ty: U::TY}]},
             ]),
             T, U);
impl HasSchema for std::string::String {
    const TY: Ty = Ty {
        name: "String",
        args: &[],
    };
    const BUNDLE: TyDefBundle = TyDefBundle {
        def: TyDef {
            ty: Self::TY,
            body: <Vec<u8> as HasSchema>::BUNDLE.def.body,
        },
        child_defs: <Vec<u8> as HasSchema>::BUNDLE.child_defs,
    };
}
macro_rules! impl_tuple {
    ($n:literal, $({$t:ident, $ti:literal}),*) => {
        impl_schema!(std::concat!("Tuple", $n), ($($t),*),
                     Body::Struct(&[
                         $(Field{
                             name: std::stringify!($ti),
                             ty: $t::TY
                         }),*
                     ]), $($t),*);
    };
}
impl_tuple!(2, {T0, 0}, {T1, 1});
impl_tuple!(3, {T0, 0}, {T1, 1}, {T2, 2});
impl_tuple!(4, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3});
impl_tuple!(5, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3}, {T4, 4});
impl_tuple!(6, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3}, {T4, 4}, {T5, 5});
impl_tuple!(7, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3}, {T4, 4}, {T5, 5}, {T6, 6});
impl_tuple!(8, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3}, {T4, 4}, {T5, 5}, {T6, 6}, {T7, 7});
impl_tuple!(9, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3}, {T4, 4}, {T5, 5}, {T6, 6}, {T7, 7}, {T8, 8});
impl_tuple!(10, {T0, 0}, {T1, 1}, {T2, 2}, {T3, 3}, {T4, 4}, {T5, 5}, {T6, 6}, {T7, 7}, {T8, 8}, {T9, 9});
