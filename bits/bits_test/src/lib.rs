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

//! Dummy crate that exists only to test the bits and bits_derive crates.
//!
//! Sadly, they can't be tested from within those crates. bits_derive
//! generates instances for the trait named `::bits::Bits`. From within
//! the `bits` crate, no such trait exists: it only exists by that name
//! from outside the crate. So to test bits_derive, we need to do it from
//! outside that crate.

#[cfg(test)]
mod tests {
    use bitvec::field::BitField;
    use bitvec::order::Lsb0;
    use bitvec::view::BitView;

    use bits::{serde_as_bits, Bits};
    use bits_derive::Bits;

    // Test derive(Bits) on an enum
    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    enum SomeEnum {
        A,
        B(bool),
        C { a: bool, b: bool },
    }

    #[track_caller]
    fn unpack<T>(v: u64) -> T
    where
        T: Bits,
    {
        assert!(
            (&v.view_bits::<Lsb0>()[T::SIZE..]).any() == false,
            "None of the bits outside of the type bit width should be set.\n\
             Type bit width: {}\n\
             Bits beyond bit {}: {:b}",
            T::SIZE,
            T::SIZE,
            &[v].view_bits::<Lsb0>()[T::SIZE..],
        );
        T::unpack(&v.view_bits()[0..T::SIZE])
    }

    #[track_caller]
    fn pack<T>(v: T) -> u64
    where
        T: Bits,
    {
        Bits::pack_u64(&v)
    }

    #[test]
    fn test_derive_enum() {
        assert_eq!(unpack::<SomeEnum>(0b0000), SomeEnum::A);
        assert_eq!(unpack::<SomeEnum>(0b0100), SomeEnum::B(false));
        assert_eq!(unpack::<SomeEnum>(0b0101), SomeEnum::B(true));
        assert_eq!(
            unpack::<SomeEnum>(0b1000),
            SomeEnum::C { a: false, b: false }
        );
        assert_eq!(
            unpack::<SomeEnum>(0b1001),
            SomeEnum::C { a: false, b: true }
        );
        assert_eq!(
            unpack::<SomeEnum>(0b1010),
            SomeEnum::C { a: true, b: false }
        );
        assert_eq!(unpack::<SomeEnum>(0b1011), SomeEnum::C { a: true, b: true });

        assert_eq!(0b0000, pack(SomeEnum::A));
        assert_eq!(0b0100, pack(SomeEnum::B(false)));
        assert_eq!(0b0101, pack(SomeEnum::B(true)));
        assert_eq!(0b1000, pack(SomeEnum::C { a: false, b: false }));
        assert_eq!(0b1001, pack(SomeEnum::C { a: false, b: true }));
        assert_eq!(0b1010, pack(SomeEnum::C { a: true, b: false }));
        assert_eq!(0b1011, pack(SomeEnum::C { a: true, b: true }));

        bits::test_roundtrips_conditional::<SomeEnum>(&|u| u.load_le::<u64>() < 12);
    }

    // A test case that revealed pack() implementation bugs in the past.
    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    enum Enum2 {
        A([bool; 3]),
        B,
    }

    #[test]
    fn test_derive_enum2() {
        bits::test_roundtrips::<Enum2>();
    }

    // Test derive(Bits) on a named struct.
    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    struct SomeStruct {
        x: bool,
        y: bool,
    }
    serde_as_bits!(SomeStruct);

    #[test]
    fn test_derive_struct() {
        assert_eq!(
            unpack::<SomeStruct>(0b00),
            SomeStruct { x: false, y: false }
        );
        assert_eq!(unpack::<SomeStruct>(0b01), SomeStruct { x: false, y: true });
        assert_eq!(unpack::<SomeStruct>(0b10), SomeStruct { x: true, y: false });
        assert_eq!(unpack::<SomeStruct>(0b11), SomeStruct { x: true, y: true });

        assert_eq!(0b00, pack(SomeStruct { x: false, y: false }));
        assert_eq!(0b01, pack(SomeStruct { x: false, y: true }));
        assert_eq!(0b10, pack(SomeStruct { x: true, y: false }));
        assert_eq!(0b11, pack(SomeStruct { x: true, y: true }));

        bits::test_roundtrips::<SomeStruct>();
    }

    // Test derive(Bits) on an unnamed struct.
    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    struct SomeUnnamedStruct(pub bool, pub bool);
    serde_as_bits!(SomeUnnamedStruct);

    #[test]
    fn test_derive_unnamed_struct() {
        assert_eq!(
            unpack::<SomeUnnamedStruct>(0b00),
            SomeUnnamedStruct(false, false)
        );
        assert_eq!(
            unpack::<SomeUnnamedStruct>(0b01),
            SomeUnnamedStruct(false, true)
        );
        assert_eq!(
            unpack::<SomeUnnamedStruct>(0b10),
            SomeUnnamedStruct(true, false)
        );
        assert_eq!(
            unpack::<SomeUnnamedStruct>(0b11),
            SomeUnnamedStruct(true, true)
        );

        assert_eq!(0b00, pack(SomeUnnamedStruct(false, false)));
        assert_eq!(0b01, pack(SomeUnnamedStruct(false, true)));
        assert_eq!(0b10, pack(SomeUnnamedStruct(true, false)));
        assert_eq!(0b11, pack(SomeUnnamedStruct(true, true)));

        bits::test_roundtrips::<SomeUnnamedStruct>();
    }

    // Test derive(Bits) on a type with generics
    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    struct SomeGenericType<T>(pub T);
    serde_as_bits!(SomeGenericType<T: Copy>);

    // Due to https://github.com/rust-lang/rust/issues/66582 we need a "T: Copy"
    // constraint here, even though it ought to be included automatically in the
    // "where" clause of #[derive(Bits)].
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Bits)]
    struct SomeNestedGenericType<T: Copy>(pub SomeGenericType<T>);

    #[test]
    fn test_derive_generic_struct() {
        // SomeGenericType<bool>
        assert_eq!(unpack::<SomeGenericType<_>>(0b0), SomeGenericType(false));
        assert_eq!(unpack::<SomeGenericType<_>>(0b1), SomeGenericType(true));

        assert_eq!(0b0, pack(SomeGenericType(false)));
        assert_eq!(0b1, pack(SomeGenericType(true)));

        // SomeNestedGenericType<bool>
        assert_eq!(
            unpack::<SomeNestedGenericType<_>>(0b0),
            SomeNestedGenericType(SomeGenericType(false))
        );
        assert_eq!(
            unpack::<SomeNestedGenericType<_>>(0b1),
            SomeNestedGenericType(SomeGenericType(true))
        );

        assert_eq!(0b0, pack(SomeNestedGenericType(SomeGenericType(false))));
        assert_eq!(0b1, pack(SomeNestedGenericType(SomeGenericType(true))));
    }

    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    enum EnumWithUnimplemented {
        A(bool),
        #[unimplemented]
        B {
            a: bool,
            b: bool,
        },
    }

    #[test]
    fn test_derived_nopanic() {
        assert_eq!(
            unpack::<EnumWithUnimplemented>(0b001),
            EnumWithUnimplemented::A(true)
        );
    }

    #[test]
    #[should_panic]
    fn test_derived_panic() {
        assert_eq!(
            unpack::<EnumWithUnimplemented>(0b100),
            EnumWithUnimplemented::B { a: false, b: false }
        );
    }

    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    struct BigStruct {
        x: u32,
        y: u32,
        z: u32,
    }

    #[test]
    fn test_derive_big_struct() {
        assert_eq!(
            BigStruct::unpack(&[0x87654321FEDCBA09u64, 0x0000000012345678].view_bits()[0..96]),
            BigStruct {
                x: 0x12345678,
                y: 0x87654321,
                z: 0xFEDCBA09
            }
        );
        bits::test_roundtrips::<BigStruct>();
    }
}
