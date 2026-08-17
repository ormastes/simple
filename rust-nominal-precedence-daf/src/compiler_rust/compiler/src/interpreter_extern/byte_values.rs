//! Shared byte extraction for interpreter extern consumers.
//!
//! A typed byte literal is represented as `Value::UInt { width: 8 }`, while
//! older call sites and arithmetic still produce `Value::Int`. Consumers
//! must accept both spellings, including packed and immutable arrays, without
//! treating raw-byte `StrBytes` as an array. Keeping this conversion in one
//! place prevents crypto, I/O and conversion externs from silently dropping
//! packed bytes in different ways.

use crate::value::Value;

/// Extract a byte from one numeric array element.
pub(crate) fn byte(value: &Value) -> Option<u8> {
    match value {
        Value::Int(value) => u8::try_from(*value).ok(),
        Value::UInt { value, width: 8 } => u8::try_from(*value).ok(),
        _ => None,
    }
}

/// Extract a language `[u8]` from packed, boxed, frozen, or fixed-size arrays.
///
/// `StrBytes` intentionally does not match here: it is text-like raw UTF-8
/// data and callers that accept it (for example SHA-256) must opt in
/// explicitly so byte-array APIs do not erase the distinction.
pub(crate) fn array_bytes(value: &Value) -> Option<Vec<u8>> {
    let values = match value {
        Value::ByteArray(values) | Value::FrozenByteArray(values) => return Some(values.as_ref().clone()),
        Value::Array(values) | Value::FrozenArray(values) => values.as_slice(),
        Value::FixedSizeArray { data, .. } => data.as_slice(),
        _ => return None,
    };
    values.iter().map(byte).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use super::super::{conversion, crypto, sha256, sha512};

    #[test]
    fn extracts_int_uint_and_frozen_byte_arrays() {
        let value = Value::FrozenArray(Arc::new(vec![Value::Int(0x41), Value::UInt { value: 0x42, width: 8 }]));
        assert_eq!(array_bytes(&value), Some(vec![0x41, 0x42]));
        assert_eq!(
            array_bytes(&Value::byte_array(vec![0x43, 0x44])),
            Some(vec![0x43, 0x44])
        );
        assert_eq!(
            array_bytes(&Value::frozen_byte_array(vec![0x45, 0x46])),
            Some(vec![0x45, 0x46])
        );
    }

    #[test]
    fn rejects_non_byte_values_and_str_bytes() {
        assert_eq!(array_bytes(&Value::array(vec![Value::Int(256)])), None);
        assert_eq!(
            array_bytes(&Value::array(vec![Value::UInt { value: 1, width: 16 }])),
            None
        );
        assert_eq!(array_bytes(&Value::StrBytes(Arc::new(vec![0xff]))), None);
    }

    #[test]
    fn packed_arrays_reach_direct_consumers() {
        let packed = Value::byte_array(b"ok".to_vec());
        assert_eq!(
            conversion::rt_bytes_to_text_fn(std::slice::from_ref(&packed)).unwrap(),
            Value::text("ok")
        );
        assert_eq!(
            conversion::bytes_to_u32_le_fn(&[Value::byte_array(vec![1, 2, 3, 4])]).unwrap(),
            Value::Int(0x0403_0201)
        );
        assert_eq!(
            crypto::rt_base64_encode(std::slice::from_ref(&packed)).unwrap(),
            Value::text("b2s=")
        );

        let handle = match sha256::rt_sha256_new(&[]).unwrap() {
            Value::Int(handle) => handle,
            other => panic!("expected SHA-256 handle, got {other:?}"),
        };
        sha256::rt_sha256_write(&[Value::Int(handle), packed.clone(), Value::Int(2)]).unwrap();
        assert!(sha256::rt_sha256_finish(&[Value::Int(handle)]).is_ok());

        assert!(sha512::rt_sha512_hash(&[packed.clone(), Value::Int(0)]).is_ok());
    }
}
