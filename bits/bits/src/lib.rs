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

//! Moving between Rust types and bit vectors.

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

use bitvec::field::BitField;
use bitvec::order::Lsb0;
use bitvec::slice::BitSlice;
use bitvec::store::BitStore;
use bitvec::vec::BitVec;
use bitvec::view::BitView;
use rand_core::{RngCore, SeedableRng};
use rand_xoshiro::Xoshiro256StarStar;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;
use std::panic::{self, RefUnwindSafe};

#[doc(hidden)]
pub mod reexport {
    pub use bitvec;
    pub use schema;
    pub use serde;
}

pub type Slice<S> = BitSlice<S, Lsb0>;
pub type BitVector<S> = BitVec<S, Lsb0>;

/// std::cmp::max, formulated as a 'const fn', for use in
/// `const SIZE`.
///
/// In 1.46.0 `std::cmp::max` is not a `const fn`, I think, as `const fn` does
/// not support traits yet.  Not really sure what is a good tracking issue for
/// this potential change.  Maybe https://github.com/rust-lang/rust/issues/57563
pub const fn const_max(x: usize, y: usize) -> usize {
    if x > y {
        x
    } else {
        y
    }
}

/// Determines the number of bits required to represent `x`.
pub const fn bit_size(x: usize) -> usize {
    let x = x as u64; // Number of bits now predictable
    (64 - x.leading_zeros()) as usize
}

/// Given a Bits value, return the number of bits used by the encoding.
pub fn value_size<T>(_: &T) -> usize
where
    T: Bits,
{
    T::SIZE
}

#[derive(Clone, Copy, Debug)]
pub struct BitsRangeErr {
    pub ty: &'static str,
    pub val: u64,
    pub max: u64,
}

/// Bits type trait.
///
pub trait Bits {
    /// Number of bits required to represent this type in packed form.
    // TODO(sgrayson) this limits more complex simulations
    const SIZE: usize;

    /// Unpacks an object from `bits`. Size of `bits` must be exactly `SIZE`.
    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self;

    /// Packs an object into the destination. Size of `dst` must be exactly
    /// `SIZE`.
    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>);

    /// Packs an object into a newly allocated bitvec.
    fn pack<S: BitStore>(&self) -> BitVector<S> {
        let mut result = BitVector::<S>::new();
        result.resize(Self::SIZE, false);
        self.pack_to(&mut result);
        result
    }

    /// Unpacks an object from a u64.
    ///
    /// Requires SIZE<=64.
    ///
    /// DEPRECATED: Use unpack() instead.
    fn unpack_u64(bits: u64) -> Self
    where
        Self: Bits + Sized,
    {
        // Not sure why, but I can not make this into a `const`.
        let size: usize = <Self as Bits>::SIZE;
        assert!(size <= 64);
        <Self as Bits>::unpack(&bits.view_bits()[0..size])
    }

    /// Packs an object into a u64.
    ///
    /// Requires SIZE<=64.
    ///
    /// DEPRECATED: Use pack() instead.
    fn pack_u64(&self) -> u64
    where
        Self: Bits + Sized,
    {
        // Not sure why, but I can not make this into a `const`.
        let size: usize = <Self as Bits>::SIZE;
        assert!(size <= 64);
        let mut store = 0u64;
        self.pack_to(&mut store.view_bits_mut()[0..size]);
        store
    }
}

/// Returns true if A::unpack(x) doesn't panic.
///
/// Intended to be used as the argument to test_roundtrips_conditional.
pub fn unpack_doesnt_panic<A, S>(x: &Slice<S>) -> bool
where
    A: Bits,
    S: BitStore + RefUnwindSafe,
{
    panic::catch_unwind(|| A::unpack(x)).is_ok()
}

/// General-purpose test that an instance of Bits roundtrips
/// in the sense that
///    unpack(pack(x)) == x
///
/// See test_roundtrips_conditional for more details.
pub fn test_roundtrips<A>()
where
    A: Bits + Eq + std::fmt::Debug,
{
    test_roundtrips_conditional::<A>(&|_| true);
}

/// General-purpose test that an instance of Bits roundtrips
/// in the sense that
///    unpack(pack(x)) == x
/// We do not check the reverse direction (pack(unpack(x)) == x)
/// since that is not guaranteed by Bits instances.
///
/// This is tested for a range of different x values. The x
/// values are constructed by calling unpack() on various u64
/// numbers. If some unpack() numbers are disallowed (for example
/// if unpack() panics on some of them), you may filter them out
/// by returning false from 'predicate'.
///
/// The tested u64 values are generated as follows:
///  * for small bitwidths, we test exhaustively among u64s that
///    fit in the bitwidth.
///  * for large bitwidths, we sample randomly among u64s that
///    fit in the bitwidth.
pub fn test_roundtrips_conditional<A>(predicate: &dyn Fn(&Slice<u64>) -> bool)
where
    A: Bits + Eq + std::fmt::Debug,
{
    if A::SIZE < 10 {
        for v in 0..(1 << A::SIZE) {
            let slice = &v.view_bits()[0..A::SIZE];
            if predicate(slice) {
                let a = A::unpack(slice);
                assert_eq!(a, A::unpack(&a.pack::<u32>()), "{}", slice);
            }
        }
    } else {
        // Randomly sample, 1024 times.
        let mut rng = Xoshiro256StarStar::seed_from_u64(0);
        for _ in 0..1024 {
            let mut vec = vec![0u64; (A::SIZE + 63) / 64];
            for x in vec.iter_mut() {
                *x = rng.next_u64();
            }
            let slice = &vec.view_bits()[0..A::SIZE];
            if predicate(slice) {
                let a = A::unpack(slice);
                assert_eq!(a, A::unpack(&a.pack::<u32>()), "{}", slice);
            }
        }
    }
}

/// `()` is packed as a zero-bit type. It appears in certain places where a
/// variant is not required.
impl Bits for () {
    const SIZE: usize = 0;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
    }
}

/// Bool is packed as a single bit, in the way you'd expect.
impl Bits for bool {
    const SIZE: usize = 1;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        bits[0]
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.set(0, *self);
    }
}

impl Bits for u8 {
    const SIZE: usize = 8;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        bits.load_le()
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.store_le(*self);
    }
}

impl Bits for u16 {
    const SIZE: usize = 16;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        bits.load_le()
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.store_le(*self);
    }
}

impl Bits for u32 {
    const SIZE: usize = 32;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        bits.load_le()
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.store_le(*self);
    }
}

impl Bits for u64 {
    const SIZE: usize = 64;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        bits.load_le()
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.store_le(*self);
    }
}

impl Bits for f32 {
    const SIZE: usize = 32;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        f32::from_bits(bits.load_le())
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.store_le((*self).to_bits());
    }
}

impl Bits for f64 {
    const SIZE: usize = 64;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), <Self as Bits>::SIZE);
        f64::from_bits(bits.load_le())
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), <Self as Bits>::SIZE);
        dst.store_le((*self).to_bits());
    }
}

impl<A> Bits for (A,)
where
    A: Bits,
{
    const SIZE: usize = A::SIZE;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        assert_eq!(bits.len(), Self::SIZE);
        (A::unpack(bits),)
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), Self::SIZE);
        self.0.pack_to(dst)
    }
}

/// Tuples are encoded with the leftmost element in more significant positions
/// and the rightmost element in less significant positions.
#[macro_export]
macro_rules! bits_impl_tuple {
    (
        $( $v:ident : $t:ident ),*
    ) => {
        impl< $($t),* > Bits for ($($t),*)
        where
            $( $t: Bits ),*
        {
            const SIZE: usize = $($t::SIZE +)* 0;

            fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
                assert_eq!(bits.len(), Self::SIZE);
                let mut component_end = Self::SIZE;
                $(
                    let component_start = component_end - $t::SIZE;
                    let $v = $t::unpack(&bits[component_start..component_end]);
                    component_end = component_start;
                )*
                let _unused = component_end; // Suppress warning
                    ($($v),*)
            }

            fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
                assert_eq!(dst.len(), Self::SIZE);
                let ($($v),*) = self;
                let mut component_end = Self::SIZE;
                $(
                    let component_start = component_end - $t::SIZE;
                    $v.pack_to(&mut dst[component_start..component_end]);
                    component_end = component_start;
                )*
                let _unused = component_end; // Suppress warning
            }
        }
    };
}

bits_impl_tuple!(t0: T0, t1: T1);
bits_impl_tuple!(t0: T0, t1: T1, t2: T2);
bits_impl_tuple!(t0: T0, t1: T1, t2: T2, t3: T3);
bits_impl_tuple!(t0: T0, t1: T1, t2: T2, t3: T3, t4: T4);
bits_impl_tuple!(t0: T0, t1: T1, t2: T2, t3: T3, t4: T4, t5: T5);
bits_impl_tuple!(t0: T0, t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6);
bits_impl_tuple!(
    t0: T0,
    t1: T1,
    t2: T2,
    t3: T3,
    t4: T4,
    t5: T5,
    t6: T6,
    t7: T7
);
bits_impl_tuple!(
    t0: T0,
    t1: T1,
    t2: T2,
    t3: T3,
    t4: T4,
    t5: T5,
    t6: T6,
    t7: T7,
    t8: T8
);
bits_impl_tuple!(
    t0: T0,
    t1: T1,
    t2: T2,
    t3: T3,
    t4: T4,
    t5: T5,
    t6: T6,
    t7: T7,
    t8: T8,
    t9: T9
);
bits_impl_tuple!(
    t0: T0,
    t1: T1,
    t2: T2,
    t3: T3,
    t4: T4,
    t5: T5,
    t6: T6,
    t7: T7,
    t8: T8,
    t9: T9,
    t10: T10
);
bits_impl_tuple!(
    t0: T0,
    t1: T1,
    t2: T2,
    t3: T3,
    t4: T4,
    t5: T5,
    t6: T6,
    t7: T7,
    t8: T8,
    t9: T9,
    t10: T10,
    t11: T11
);

impl<A, const N: usize> Bits for [A; N]
where
    A: Bits,
{
    const SIZE: usize = N * A::SIZE;

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        use std::convert::TryInto;
        let Ok(ret) = (0..N)
            .map(|i| A::unpack(&bits[i * A::SIZE..(i + 1) * A::SIZE]))
            .collect::<Vec<A>>()
            .try_into()
        else {
            panic!("Length mismatch can't happen!");
        };
        ret
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        for i in 0..N {
            self[i as usize].pack_to(&mut dst[i * A::SIZE..(i + 1) * A::SIZE]);
        }
    }
}

/// Option is encoded by attaching a `Some` flag as the MSB.
impl<A> Bits for Option<A>
where
    A: Bits,
{
    const SIZE: usize = A::SIZE + 1;
    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        if bits[Self::SIZE - 1] {
            Some(A::unpack(&bits[0..A::SIZE]))
        } else {
            None
        }
    }
    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        assert_eq!(dst.len(), Self::SIZE);
        match self {
            Some(a) => {
                dst.set(Self::SIZE - 1, true);
                a.pack_to(&mut dst[0..Self::SIZE - 1]);
            }
            None => {
                dst.fill(false);
            }
        }
    }
}

/// A specialization of `Bits` for types that pack into numerically low values
/// in their encoded space. This enables types to be used with the Packed
/// containers.
pub trait LimitedRange: Bits {
    /// Produces the largest value that can be produced by packing this type.
    const MAX_ENCODING: u64;
}

/// Newtype for `Option` that enables a packed encoding for limited-range types.
/// `None` is encoded as one greater than the largest encoding for `T`.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub struct PackedOption<T>(pub Option<T>);

impl<T> Bits for PackedOption<T>
where
    T: LimitedRange,
{
    const SIZE: usize = bit_size(T::MAX_ENCODING as usize + 1);

    fn unpack<S: BitStore>(bits: &Slice<S>) -> Self {
        let value: u64 = bits.load_le();
        PackedOption(if value == T::MAX_ENCODING + 1 {
            None
        } else {
            Some(T::unpack(&bits[0..T::SIZE]))
        })
    }

    fn pack_to<S: BitStore>(&self, dst: &mut Slice<S>) {
        match &self.0 {
            None => dst.store_le(T::MAX_ENCODING + 1),
            Some(t) => t.pack_to(&mut dst[0..T::SIZE]),
        }
    }
}

pub struct BitsFromU64Visitor<T>
where
    T: Bits,
{
    _target: PhantomData<T>,
}

#[allow(clippy::new_without_default)]
impl<T> BitsFromU64Visitor<T>
where
    T: Bits,
{
    pub fn new() -> Self {
        let size = <T as Bits>::SIZE;
        assert!(
            size <= 64,
            "`BitsFromU64Visitor` only works for sizes of up to 64 bits.\n\
             `{}` size is: {}",
            std::any::type_name::<T>(),
            size,
        );
        BitsFromU64Visitor {
            _target: PhantomData,
        }
    }
}

impl<'de, T> serde::de::Visitor<'de> for BitsFromU64Visitor<T>
where
    T: Bits,
{
    type Value = T;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a {}-bit number", <T as Bits>::SIZE)
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let size = <T as Bits>::SIZE;

        if size < 64 && value >= (1u64 << size) {
            Err(E::custom(format!(
                "{}-bit number out of range: {}",
                size, value
            )))
        } else {
            let bits = &value.view_bits()[0..size];
            Ok(T::unpack(bits))
        }
    }
}

/// Defines a newtype for a primitive type with a restricted number of
/// implemented bits. The expected syntax is a single-field newtype with the
/// number of bits folowing in brackets.
///
/// ```
/// use bits::bits_newtype;
///
/// bits_newtype! {
///     /// A three-bit type.
///     pub struct ThreeBits(u8) [3];
/// }
///
/// const A_CONSTANT: usize = 12;
///
/// bits_newtype! {
///     /// A type whose width is given by a constant.
///     pub struct TwelveBits(u16) [A_CONSTANT];
///     /// And an expression:
///     pub struct MoreBits(u32) [A_CONSTANT*2];
/// }
///
/// # fn main() {}
///
/// ```
///
/// In addition to the type `T`, this generates the following instances:
///
/// - `Copy`, `Clone`, `Eq`, `PartialEq`, `Debug`, and `Default` are
///   automatically derived.
/// - [`Bits`], and [`HasSchema`] for `T`
/// - `From<T>` for the underlying primitive integer type.
/// - `HasSchema` to allow the type to participate in the whitebox API.
/// - `Serialize` and `Deserialize` (from `serde`) for `T`.
///
/// [`Bits`]: ../trait.Bits.html
#[macro_export]
macro_rules! bits_newtype {
    (
        $(
            $(#[$attr:meta])*
            pub struct $name:ident < $( $phant:ident : $trt:path ),* $(,)*>
                ($type:ident) [$bits:expr];
        )*
    ) => {
        $crate::bits_newtype! {
            $(@impl [attrs $($attr)*]
                    [phantom $( $phant : $trt ),*]
                    [barename $name]
                    [wrapped $type]
                    [bits $bits])*
        }
    };

    (
        $(
            $(#[$attr:meta])*
            pub struct $name:ident($type:ident) [ $bits:expr ];
        )*
    ) => {
        $crate::bits_newtype! {
            $(@impl [attrs $($attr)*]
                    [phantom ]
                    [barename $name]
                    [wrapped $type]
                    [bits $bits])*
        }
    };
    ($(@impl [attrs $($attr:meta)*]
             [phantom $( $phant:ident : $trt:path ),* ]
             [barename $name:ident]
             [wrapped $type:ty]
             [bits $bits:expr])*) => {
        $(
            $(#[$attr])*
            #[derive(Eq, PartialEq, Debug, ::smart_default::SmartDefault)]
            pub struct $name< $($phant),* > (
                $type, $( ::std::marker::PhantomData<$phant> ),*
            );
            impl< $($phant),* > Copy for $name< $($phant),* > {}
            impl< $($phant),* > Clone for $name< $($phant),* > {
                fn clone(&self) -> Self { *self }
            }

            impl< $($phant : $trt),* >
                ::std::convert::TryFrom<$type>
                for $name< $($phant),* >
            {
                type Error = $crate::BitsRangeErr;

                /// Converts `val` into `Self` if the value is within range.
                #[inline]
                fn try_from(val: $type) -> Result<Self, Self::Error> {
                    let size = <Self as ::bits::Bits>::SIZE;
                    let mask = if size < 64 {
                        (1 << size) - 1
                    } else {
                        std::u64::MAX
                    };
                    let val64 = val as u64;
                    if val64 <= mask {
                        Ok($name(
                            val,
                            $( ::std::marker::PhantomData::<$phant> ),*
                        ))
                    } else {
                        Err(Self::Error {
                            ty: ::std::stringify!($name),
                            val: val64,
                            max: mask as u64,
                        })
                    }
                }
            }

            impl< $($phant: $trt),* >
                ::bits::Bits
                for $name< $($phant),* >
            {
                const SIZE: usize = $bits;

                #[inline]
                fn unpack<__BitsNewTypeS: ::bits::reexport::bitvec::store::BitStore>(bits: &::bits::Slice<__BitsNewTypeS>) -> Self {
                    let expected_size =
                        <Self as ::bits::Bits>::SIZE;
                    assert!(
                        bits.len() == expected_size,
                        "{}::unpack(): Bit size mismatch.\n\
                         Expected bit size: {}\n\
                         Actual bit size: {}",
                        stringify!($name),
                        expected_size,
                        bits.len(),
                    );

                    use $crate::reexport::bitvec::field::BitField;
                    $name(bits.load_le(),
                          $( ::std::marker::PhantomData::<$phant> ),* )
                }

                #[inline]
                fn pack_to<__BitsNewTypeS: ::bits::reexport::bitvec::store::BitStore>(&self, dst: &mut ::bits::Slice<__BitsNewTypeS>) {
                    let expected_size =
                        <Self as ::bits::Bits>::SIZE;
                    assert!(
                        dst.len() == expected_size,
                        "{}::pack_to(): Target bit slice size mismatch.\n\
                         Expected slice bit size: {}\n\
                         Actual slice bit size: {}",
                        stringify!($name),
                        expected_size,
                        dst.len(),
                    );

                    use $crate::reexport::bitvec::field::BitField;
                    dst.store_le(self.0);
                }
            }

            impl< $($phant: $trt),* > From<$name< $($phant),* >> for $type {
                #[inline]
                fn from(x: $name< $($phant),* >) -> Self {
                    x.0
                }
            }

            $crate::serde_as_bits!( $name< $( $phant: $trt ),* > );
        )*
    };
}

#[macro_export]
macro_rules! serde_as_bits {
    // serde_as_bits!(Foo<T: Baz, U: Quux>);
    ($( $name:ident< $($param:ident: $trt:path),* > );* $(;)*) => {
        $crate::serde_as_bits! {
            $( @impl
                [name $name]
                [params $( $param : $trt ),* ]
            );*
        }
    };

    ($( $name:ident );* $(;)*) => {
        $crate::serde_as_bits! {
            $( @impl
                [name $name]
                [params ]
            );*
        }
    };

    ($( @impl
        [name $name:ident]
        [params $( $param:ident : $trt:path ),* ]
    );*) => {
        $(
            impl< $($param: $trt),* >
                $crate::reexport::serde::ser::Serialize
                for $name< $($param),* >
            where
                $name< $($param),*>: $crate::Bits
            {
                fn serialize<S>(
                    &self,
                    serializer: S,
                ) -> Result<S::Ok, S::Error>
                where
                    S: $crate::reexport::serde::ser::Serializer,
                {
                    let v = <Self as $crate::Bits>::pack_u64(self);
                    serializer.serialize_u64(v)
                }
            }

            impl<'de, $($param: $trt),* >
                $crate::reexport::serde::de::Deserialize<'de>
                for $name< $($param),* >
            where
                $name< $($param),* >: $crate::Bits
            {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: $crate::reexport::serde::de::Deserializer<'de>,
                {
                    deserializer.deserialize_u64(
                        $crate::BitsFromU64Visitor::new()
                    )
                }
            }

            impl< $($param: $trt + $crate::reexport::schema::HasSchema),* >
                $crate::reexport::schema::HasSchema
                for $name< $($param),* >
            where
                $name< $($param),* >: $crate::Bits
            {
                const TY: $crate::reexport::schema::Ty =
                    $crate::reexport::schema::Ty {
                        name: ::std::concat!(
                                  ::std::module_path!(),
                                  "::",
                                  ::std::stringify!($name)
                                ),
                        args: &[ $(&$param::TY),* ],
                    };

                const BUNDLE: $crate::reexport::schema::TyDefBundle =
                    $crate::reexport::schema::TyDefBundle {
                        def: $crate::reexport::schema::TyDef {
                            ty: Self::TY,
                            body: $crate::reexport::schema::Body::Bits(
                                <Self as $crate::Bits>::SIZE as u32
                            ),
                        },
                        child_defs: || &[ $(&$param::BUNDLE),* ],
                    };
            }
        )*
    };
}
