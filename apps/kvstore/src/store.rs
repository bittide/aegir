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

//! implementation of a serializable store for key-value pais.
use crate::{Data, DATA_SIZE};
use bits_derive::Bits;

const MAX_STORE_SIZE: usize = 1024;

#[derive(Bits, Debug)]
pub struct Store {
    data: [(u64, Data); MAX_STORE_SIZE],
    top: u64,
}

impl Store {
    /// create a new, empty store
    pub fn new() -> Self {
        Self {
            data: [(u64::MAX, [0; DATA_SIZE]); MAX_STORE_SIZE],
            top: 0,
        }
    }

    /// create a new store, with pre-defined data inserted.
    #[cfg(test)]
    pub fn init_predefined() -> Self {
        const STORE_SIZE: usize = 10;
        assert!(STORE_SIZE < MAX_STORE_SIZE, "Store size exceeded");
        let mut store = Store::new();
        for x in 0..STORE_SIZE {
            store.insert(&(x as u64), [x as u8; DATA_SIZE]);
        }
        store
    }

    /// return the value for key, or None if key does not exist.
    pub fn get(&self, key: &u64) -> Option<Data> {
        let kv = self.data.iter().find(|&(k, _)| k == key);
        if let Some(&(_, v)) = kv {
            Some(v.clone())
        } else {
            None
        }
    }

    /// modify the value for key and return the old value. Or return None if
    /// the key does not exist.
    pub fn modify(&mut self, key: &u64, data: Data) -> Option<Data> {
        for (k, v) in self.data.iter_mut() {
            if k == key {
                let tmp = v.clone();
                *v = data;
                return Some(tmp);
            }
        }
        None
    }

    pub fn insert(&mut self, key: &u64, data: Data) -> Option<Data> {
        if let Some(_) = self.get(key) {
            None
        } else {
            assert!((self.top as usize) < MAX_STORE_SIZE, "Exceeded store size");
            self.data[self.top as usize] = (*key, data);
            self.top += 1;
            Some(data)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Store;
    use crate::{Data, DATA_SIZE};
    use bits;
    use bits::Bits;
    use bitvec::prelude::*;
    use std::convert::TryInto;

    #[test]
    fn test_get() {
        let store = Store::init_predefined();
        for i in 0..store.data.len() {
            if let Some(data) = store.get(&(i as u64)) {
                assert_eq!(data, [i as u8; DATA_SIZE]);
            }
        }
        println!("test_get: {:?}", store)
    }

    #[test]
    fn test_insert() {
        let mut store = Store::init_predefined();
        assert_eq!(store.insert(&1, [5; DATA_SIZE]), None);
        assert_eq!(store.insert(&11, [5; DATA_SIZE]), Some([5; DATA_SIZE]));
        assert_eq!(store.get(&11), Some([5; DATA_SIZE]));
        println!("test_insert: {:?}", store)
    }

    #[test]
    fn test_modify() {
        let mut store = Store::init_predefined();
        assert_eq!(store.modify(&13, [13; DATA_SIZE]), None);
        let expected_val: Data = vec![3, 3, 3, 15, 3, 3, 3, 3, 3, 3].try_into().unwrap();
        assert_eq!(store.modify(&3, expected_val.clone()), Some([3; DATA_SIZE]));
        assert_eq!(store.get(&3), Some(expected_val));
        println!("test_modify: {:?}", store);
    }

    #[test]
    fn test_pack() {
        let mut data = bitbox![0; <Store as bits::Bits>::SIZE];
        let store = Store::init_predefined();
        store.pack_to(&mut data);
        let unpacked_store = Store::unpack(&data);
        assert_eq!(unpacked_store.get(&7), store.get(&7));
    }
}
