//! Interpreter bridges for the cache host authority (`rt_cache_host_*_v1`)
//! and the descriptor-pinned file view (`rt_file_view_*_v1`) families.
//!
//! Both families are implemented in the linked runtime crate
//! (`simple_runtime::cache_host_authority_v1`, `simple_runtime::file_view`)
//! and declared in `src/lib/common/cache_host_authority_v1.spl` and
//! `src/lib/common/io/{read_only_file_view,file_view_buffered}.spl`, but the
//! seed interpreter had no dispatch entries for them, so every cache spec that
//! opened a cache root died with `unknown extern function:
//! rt_cache_host_open_root_v1` (and the file view readers with
//! `rt_file_view_device_v1`).
//!
//! The bridges marshal exactly as the native lane does:
//! * cache host `text` arguments are expanded to `(ptr, len)` (see the
//!   "after semantic text expansion" entries in `codegen/runtime_sffi.rs`);
//! * cache host `[u8]` arguments are passed as a data pointer, and the
//!   separate length argument the Simple wrapper supplies must fit inside the
//!   array, otherwise the call is refused rather than reading past it;
//! * file view `text` arguments are tagged runtime string values.
//!
//! `rt_cache_host_pread_receipt_v1` fills a caller-owned buffer. Interpreter
//! byte arrays are shared copy-on-write, so a bare `[u8]` argument cannot be
//! written back to the caller; that call is only honored for a `&mut` borrow
//! and is otherwise refused with a named error instead of silently dropping
//! the bytes it read.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::cache_host_authority_v1 as host;
use simple_runtime::file_view as view;
use simple_runtime::value::{rt_array_get, rt_array_len_safe, rt_string_new, HeapObjectType, RuntimeValue};

fn arity(name: &str, args: &[Value], expected: usize) -> Result<(), CompileError> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(CompileError::semantic(format!(
            "{name} expects {expected} arguments, got {}",
            args.len()
        )))
    }
}

fn int(name: &str, args: &[Value], index: usize) -> Result<i64, CompileError> {
    args[index]
        .as_int()
        .map_err(|_| CompileError::semantic(format!("{name}: argument {index} must be an integer")))
}

fn text<'a>(name: &str, args: &'a [Value], index: usize) -> Result<&'a str, CompileError> {
    match &args[index] {
        Value::Str(s) => Ok(s.as_str()),
        other => Err(CompileError::semantic(format!(
            "{name}: argument {index} must be text, got {}",
            other.type_name()
        ))),
    }
}

/// `[u8]` argument at `index` with its caller-supplied length at `index + 1`.
fn bytes(name: &str, args: &[Value], index: usize) -> Result<(Vec<u8>, i64), CompileError> {
    let data = args[index].try_array_bytes().ok_or_else(|| {
        CompileError::semantic(format!(
            "{name}: argument {index} must be [u8], got {}",
            args[index].type_name()
        ))
    })?;
    let len = int(name, args, index + 1)?;
    if len < 0 || len as usize > data.len() {
        return Err(CompileError::semantic(format!(
            "{name}: length argument {len} does not fit the {}-byte array at argument {index}",
            data.len()
        )));
    }
    Ok((data, len))
}

fn tagged_text(value: &str) -> i64 {
    rt_string_new(value.as_ptr(), value.len() as u64).to_raw() as i64
}

/// A file view read returns either a runtime `[u8]` array or a small status.
fn runtime_bytes_or_nil(raw: i64) -> Value {
    let array = RuntimeValue::from_raw(raw as u64);
    if array.heap_type() != Some(HeapObjectType::Array) {
        return Value::Nil;
    }
    let length = rt_array_len_safe(array);
    let data = (0..length)
        .map(|index| (rt_array_get(array, index).to_raw() as i64 >> 3) as u8)
        .collect();
    Value::byte_array(data)
}

pub fn is_supported_name(name: &str) -> bool {
    SUPPORTED.contains(&name)
}

const SUPPORTED: &[&str] = &[
    "rt_cache_host_open_root_v1",
    "rt_cache_host_open_read_v1",
    "rt_cache_host_open_child_v1",
    "rt_cache_host_open_cas_kind_v1",
    "rt_cache_host_open_cas_shard_v1",
    "rt_cache_host_open_cas_leaf_v1",
    "rt_cache_host_begin_reader_pin_v1",
    "rt_cache_host_validate_reader_pin_v1",
    "rt_cache_host_renew_reader_pin_v1",
    "rt_cache_host_release_reader_pin_v1",
    "rt_cache_host_open_pinned_cas_v1",
    "rt_cache_host_reader_gc_begin_v1",
    "rt_cache_host_reader_gc_end_v1",
    "rt_cache_host_size_v1",
    "rt_cache_host_pread_receipt_v1",
    "rt_cache_host_secure_temp_v1",
    "rt_cache_host_write_temp_v1",
    "rt_cache_host_publish_noreplace_v1",
    "rt_cache_host_publish_retained_noreplace_v2",
    "rt_cache_host_quarantine_v1",
    "rt_cache_host_fsync_v1",
    "rt_cache_host_close_v1",
    "rt_file_view_open_beneath_no_follow_v1",
    "rt_file_view_mapping_supported_v1",
    "rt_file_view_map_copy_v1",
    "rt_file_view_pread_exact_v1",
    "rt_file_view_prefetch_v1",
    "rt_file_view_device_v1",
    "rt_file_view_inode_v1",
    "rt_file_view_size_v1",
    "rt_file_view_close_v1",
];

pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let n = name;
    let a = args;
    // SAFETY: every pointer handed to the runtime borrows a buffer owned by
    // this frame for the duration of the call, with the exact length passed.
    let result = unsafe {
        match name {
            "rt_cache_host_open_root_v1" => {
                arity(n, a, 1)?;
                let p = text(n, a, 0)?;
                host::rt_cache_host_open_root_v1(p.as_ptr(), p.len() as i64)
            }
            "rt_cache_host_open_read_v1" => {
                arity(n, a, 2)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_open_read_v1(int(n, a, 0)?, p.as_ptr(), p.len() as i64)
            }
            "rt_cache_host_open_child_v1" => {
                arity(n, a, 3)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_open_child_v1(int(n, a, 0)?, p.as_ptr(), p.len() as i64, int(n, a, 2)?)
            }
            "rt_cache_host_open_cas_kind_v1" => {
                arity(n, a, 3)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_open_cas_kind_v1(int(n, a, 0)?, p.as_ptr(), p.len() as i64, int(n, a, 2)?)
            }
            "rt_cache_host_open_cas_shard_v1" => {
                arity(n, a, 4)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_open_cas_shard_v1(
                    int(n, a, 0)?,
                    p.as_ptr(),
                    p.len() as i64,
                    int(n, a, 2)?,
                    int(n, a, 3)?,
                )
            }
            "rt_cache_host_open_cas_leaf_v1" => {
                arity(n, a, 2)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_open_cas_leaf_v1(int(n, a, 0)?, p.as_ptr(), p.len() as i64)
            }
            "rt_cache_host_begin_reader_pin_v1" => {
                arity(n, a, 13)?;
                let (m, ml) = bytes(n, a, 3)?;
                let (p, pl) = bytes(n, a, 5)?;
                let (b, bl) = bytes(n, a, 7)?;
                let (s, sl) = bytes(n, a, 9)?;
                host::rt_cache_host_begin_reader_pin_v1(
                    int(n, a, 0)?,
                    int(n, a, 1)?,
                    int(n, a, 2)?,
                    m.as_ptr(),
                    ml,
                    p.as_ptr(),
                    pl,
                    b.as_ptr(),
                    bl,
                    s.as_ptr(),
                    sl,
                    int(n, a, 11)?,
                    int(n, a, 12)?,
                )
            }
            "rt_cache_host_validate_reader_pin_v1" => {
                arity(n, a, 12)?;
                let (m, ml) = bytes(n, a, 3)?;
                let (p, pl) = bytes(n, a, 5)?;
                let (b, bl) = bytes(n, a, 7)?;
                let (s, sl) = bytes(n, a, 9)?;
                host::rt_cache_host_validate_reader_pin_v1(
                    int(n, a, 0)?,
                    int(n, a, 1)?,
                    int(n, a, 2)?,
                    m.as_ptr(),
                    ml,
                    p.as_ptr(),
                    pl,
                    b.as_ptr(),
                    bl,
                    s.as_ptr(),
                    sl,
                    int(n, a, 11)?,
                )
            }
            "rt_cache_host_renew_reader_pin_v1" => {
                arity(n, a, 3)?;
                host::rt_cache_host_renew_reader_pin_v1(int(n, a, 0)?, int(n, a, 1)?, int(n, a, 2)?)
            }
            "rt_cache_host_release_reader_pin_v1" => {
                arity(n, a, 11)?;
                let (m, ml) = bytes(n, a, 3)?;
                let (p, pl) = bytes(n, a, 5)?;
                let (b, bl) = bytes(n, a, 7)?;
                let (s, sl) = bytes(n, a, 9)?;
                host::rt_cache_host_release_reader_pin_v1(
                    int(n, a, 0)?,
                    int(n, a, 1)?,
                    int(n, a, 2)?,
                    m.as_ptr(),
                    ml,
                    p.as_ptr(),
                    pl,
                    b.as_ptr(),
                    bl,
                    s.as_ptr(),
                    sl,
                )
            }
            "rt_cache_host_open_pinned_cas_v1" => {
                arity(n, a, 4)?;
                let k = text(n, a, 1)?;
                let d = text(n, a, 2)?;
                host::rt_cache_host_open_pinned_cas_v1(
                    int(n, a, 0)?,
                    k.as_ptr(),
                    k.len() as i64,
                    d.as_ptr(),
                    d.len() as i64,
                    int(n, a, 3)?,
                )
            }
            "rt_cache_host_reader_gc_begin_v1" => {
                arity(n, a, 2)?;
                host::rt_cache_host_reader_gc_begin_v1(int(n, a, 0)?, int(n, a, 1)?)
            }
            "rt_cache_host_reader_gc_end_v1" => {
                arity(n, a, 3)?;
                host::rt_cache_host_reader_gc_end_v1(int(n, a, 0)?, int(n, a, 1)?, int(n, a, 2)?)
            }
            "rt_cache_host_size_v1" => {
                arity(n, a, 2)?;
                host::rt_cache_host_size_v1(int(n, a, 0)?, int(n, a, 1)?)
            }
            "rt_cache_host_pread_receipt_v1" => {
                arity(n, a, 4)?;
                return pread_receipt(a);
            }
            "rt_cache_host_secure_temp_v1" => {
                arity(n, a, 1)?;
                host::rt_cache_host_secure_temp_v1(int(n, a, 0)?)
            }
            "rt_cache_host_write_temp_v1" => {
                arity(n, a, 4)?;
                let (d, dl) = bytes(n, a, 2)?;
                host::rt_cache_host_write_temp_v1(int(n, a, 0)?, int(n, a, 1)?, d.as_ptr(), dl)
            }
            "rt_cache_host_publish_noreplace_v1" => {
                arity(n, a, 2)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_publish_noreplace_v1(int(n, a, 0)?, p.as_ptr(), p.len() as i64)
            }
            "rt_cache_host_publish_retained_noreplace_v2" => {
                arity(n, a, 2)?;
                let p = text(n, a, 1)?;
                host::rt_cache_host_publish_retained_noreplace_v2(int(n, a, 0)?, p.as_ptr(), p.len() as i64)
            }
            "rt_cache_host_quarantine_v1" => {
                arity(n, a, 3)?;
                let p = text(n, a, 2)?;
                host::rt_cache_host_quarantine_v1(int(n, a, 0)?, int(n, a, 1)?, p.as_ptr(), p.len() as i64)
            }
            "rt_cache_host_fsync_v1" => {
                arity(n, a, 1)?;
                host::rt_cache_host_fsync_v1(int(n, a, 0)?)
            }
            "rt_cache_host_close_v1" => {
                arity(n, a, 1)?;
                host::rt_cache_host_close_v1(int(n, a, 0)?)
            }
            "rt_file_view_open_beneath_no_follow_v1" => {
                arity(n, a, 2)?;
                let root = tagged_text(text(n, a, 0)?);
                let path = tagged_text(text(n, a, 1)?);
                view::rt_file_view_open_beneath_no_follow_v1(root, path)
            }
            "rt_file_view_mapping_supported_v1" => {
                arity(n, a, 1)?;
                return Ok(Value::Bool(view::rt_file_view_mapping_supported_v1(int(n, a, 0)?) != 0));
            }
            "rt_file_view_map_copy_v1" => {
                arity(n, a, 3)?;
                let raw = view::rt_file_view_map_copy_v1(int(n, a, 0)?, int(n, a, 1)? as u64, int(n, a, 2)? as u64);
                return Ok(runtime_bytes_or_nil(raw));
            }
            "rt_file_view_pread_exact_v1" => {
                arity(n, a, 3)?;
                let raw =
                    view::rt_file_view_pread_exact_v1(int(n, a, 0)?, int(n, a, 1)? as u64, int(n, a, 2)? as u64);
                return Ok(runtime_bytes_or_nil(raw));
            }
            "rt_file_view_prefetch_v1" => {
                arity(n, a, 3)?;
                let ok = view::rt_file_view_prefetch_v1(int(n, a, 0)?, int(n, a, 1)? as u64, int(n, a, 2)? as u64);
                return Ok(Value::Bool(ok != 0));
            }
            "rt_file_view_device_v1" => {
                arity(n, a, 1)?;
                view::rt_file_view_device_v1(int(n, a, 0)?)
            }
            "rt_file_view_inode_v1" => {
                arity(n, a, 1)?;
                view::rt_file_view_inode_v1(int(n, a, 0)?)
            }
            "rt_file_view_size_v1" => {
                arity(n, a, 1)?;
                view::rt_file_view_size_v1(int(n, a, 0)?)
            }
            "rt_file_view_close_v1" => {
                arity(n, a, 1)?;
                return Ok(Value::Bool(view::rt_file_view_close_v1(int(n, a, 0)?) != 0));
            }
            _ => return Err(super::common::unknown_function(name)),
        }
    };
    Ok(Value::Int(result))
}

/// `rt_cache_host_pread_receipt_v1(object, offset, out, capacity)`.
fn pread_receipt(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_cache_host_pread_receipt_v1";
    let Value::BorrowMut(out) = &args[2] else {
        return Err(CompileError::semantic(format!(
            "{NAME} requires a `&mut [u8]` out buffer in the interpreter: a bare [u8] argument is \
             copy-on-write here, so the bytes read could never reach the caller"
        )));
    };
    let mut buffer = {
        let current = out.inner();
        let current: &Value = &current;
        current
            .try_array_bytes()
            .ok_or_else(|| CompileError::semantic(format!("{NAME}: out buffer must be [u8]")))?
    };
    let capacity = int(NAME, args, 3)?;
    if capacity < 0 || capacity as usize > buffer.len() {
        return Err(CompileError::semantic(format!(
            "{NAME}: capacity {capacity} does not fit the {}-byte out buffer",
            buffer.len()
        )));
    }
    let status = unsafe {
        host::rt_cache_host_pread_receipt_v1(int(NAME, args, 0)?, int(NAME, args, 1)?, buffer.as_mut_ptr(), capacity)
    };
    *out.inner_mut() = Value::byte_array(buffer);
    Ok(Value::Int(status))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opens_a_real_root_and_reads_it_through_a_pinned_file_view() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().canonicalize().unwrap();
        std::fs::write(root.join("payload"), b"0123456789").unwrap();
        let root_text = root.to_string_lossy().to_string();

        let handle = dispatch("rt_cache_host_open_root_v1", &[Value::text(root_text.clone())]).unwrap();
        let handle = handle.as_int().unwrap();
        assert!(handle > 0, "a real absolute directory must open, got {handle}");
        let missing = dispatch("rt_cache_host_open_root_v1", &[Value::text("relative/root")]).unwrap();
        assert_eq!(missing.as_int().unwrap(), -1);
        assert_eq!(
            dispatch("rt_cache_host_close_v1", &[Value::Int(handle)]).unwrap().as_int().unwrap(),
            0,
            "close returns libc::close's status"
        );
        // The handle is consumed: a second close is refused.
        assert_eq!(
            dispatch("rt_cache_host_close_v1", &[Value::Int(handle)]).unwrap().as_int().unwrap(),
            -1
        );

        let descriptor = dispatch(
            "rt_file_view_open_beneath_no_follow_v1",
            &[Value::text(root_text), Value::text("payload")],
        )
        .unwrap()
        .as_int()
        .unwrap();
        assert!(descriptor >= 0, "open beneath failed: {descriptor}");
        let size = dispatch("rt_file_view_size_v1", &[Value::Int(descriptor)]).unwrap();
        assert_eq!(size.as_int().unwrap(), 10);
        assert!(dispatch("rt_file_view_device_v1", &[Value::Int(descriptor)]).unwrap().as_int().unwrap() >= 0);
        let read = dispatch(
            "rt_file_view_pread_exact_v1",
            &[Value::Int(descriptor), Value::Int(2), Value::Int(4)],
        )
        .unwrap();
        assert_eq!(read.try_array_bytes().unwrap(), b"2345");
        let closed = dispatch("rt_file_view_close_v1", &[Value::Int(descriptor)]).unwrap();
        assert!(matches!(closed, Value::Bool(true)));
        let bad = dispatch("rt_file_view_pread_exact_v1", &[Value::Int(-1), Value::Int(0), Value::Int(0)]).unwrap();
        assert!(matches!(bad, Value::Nil));
    }

    #[test]
    fn refuses_a_length_past_the_array_and_an_unborrowed_out_buffer() {
        let error = dispatch(
            "rt_cache_host_write_temp_v1",
            &[Value::Int(1), Value::Int(0), Value::byte_array(vec![1, 2]), Value::Int(3)],
        )
        .unwrap_err();
        assert!(error.to_string().contains("does not fit"));
        let error = dispatch(
            "rt_cache_host_pread_receipt_v1",
            &[Value::Int(1), Value::Int(0), Value::byte_array(vec![0; 4]), Value::Int(4)],
        )
        .unwrap_err();
        assert!(error.to_string().contains("`&mut [u8]` out buffer"));
    }
}
