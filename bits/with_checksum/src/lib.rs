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

use adler32;
use anyhow;
use bits::Bits;
use bits_derive::Bits;

fn checksum<B: Sized + bits::Bits>(bits: &B) -> anyhow::Result<u32> {
    let mut packed = bits::BitVector::<u32>::new();
    let size = <B as bits::Bits>::SIZE;
    packed.resize(size, false);
    bits.pack_to(&mut packed);
    let checksum = adler32::adler32(packed)?;
    Ok(checksum)
}

// WithChecksum wraps a bits serializable type with a checksum,
// so you can detect whether it's been corrupted during transission.
#[derive(Bits, Clone, Copy, Debug)]
pub struct WithChecksum<T>
where
    T: Bits + Sized,
{
    payload: T,
    checksum: u32,
}

impl<T> WithChecksum<T>
where
    T: Bits + Sized,
{
    pub fn new(payload: T) -> Self {
        let checksum = checksum(&payload).expect("failed to checksum");
        WithChecksum { payload, checksum }
    }

    pub fn unwrap(self) -> T {
        self.payload
    }

    pub fn borrow<'a>(&'a self) -> &'a T {
        &self.payload
    }

    pub fn is_ok(&self) -> bool {
        let checksum = checksum(&self.payload).expect("failed to checksum");
        checksum == self.checksum
    }
}

#[cfg(test)]
mod tests {
    use bits::Bits;
    use bits_derive::Bits;

    use super::WithChecksum;

    #[derive(Clone, Copy, Bits, Debug, PartialEq, Eq)]
    struct BigStruct {
        x: u32,
        y: u32,
        z: u32,
    }

    #[test]
    fn test_pack_with_checksums() {
        // Verify that we can do a round-trip packing/unpacking a struct,
        // with checksum validation.

        type Data = WithChecksum<BigStruct>;

        let value = BigStruct {
            x: 0x12345678,
            y: 0x87654321,
            z: 0xFEDCBA09,
        };

        let data = Data::new(value);
        assert!(data.is_ok(), "checksum should be valid upon creation.");

        let mut packed = Data::pack::<u32>(&data);
        let unpacked = Data::unpack(&packed);
        assert!(unpacked.is_ok(), "checksum should be valid after unpack");
        assert_eq!(
            unpacked.unwrap(),
            data.unwrap(),
            "unpacked should equal original value"
        );

        // Verify that if we corrupt the packed bits, the checksum detects the corruption.
        let bit = packed[4];
        packed.as_mut_bitslice().set(4, !bit);
        let unpacked = Data::unpack(&packed);
        assert!(!unpacked.is_ok(), "checksum should detect corruption");
    }
}
