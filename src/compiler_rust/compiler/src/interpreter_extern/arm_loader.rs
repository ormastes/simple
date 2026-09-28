//! Hosted interpreter backings for the `@cfg(arm64)` loader byte externs.
//!
//! The interpreter picks `@cfg` by `TargetArch::host()`, so on an aarch64 host
//! kernel loader code (`os/kernel/loader/byte_utils.spl`, `elf_loader.spl`,
//! `process_image.spl`) reaches the arm64 freestanding helpers. Their only
//! implementation is the bare-metal runtime
//! (`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`); these
//! handlers mirror that C byte-for-byte for the pure byte-math subset:
//! out-of-bounds reads return 0, and the ELF64 helpers require the same
//! aarch64 header shape (`e_machine == 183`, ehsize 64, phentsize 56).
//!
//! Hardware-only arm64 externs (dcache maintenance, EL0 user copy/handoff,
//! payload regions, SVC, RNDR) are deliberately not backed here.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::{rt_array_get, rt_array_len, RuntimeValue};

enum ByteView<'a> {
    Packed(&'a [u8]),
    Values(&'a [Value]),
    Raw(RuntimeValue),
    Empty,
}

impl<'a> ByteView<'a> {
    fn of(value: &'a Value) -> Self {
        match value {
            Value::ByteArray(v) | Value::FrozenByteArray(v) => ByteView::Packed(v.as_slice()),
            Value::Array(v) | Value::FrozenArray(v) => ByteView::Values(v.as_slice()),
            Value::Int(raw) => ByteView::Raw(RuntimeValue::from_raw(*raw as u64)),
            _ => ByteView::Empty,
        }
    }

    fn len(&self) -> u64 {
        match self {
            ByteView::Packed(v) => v.len() as u64,
            ByteView::Values(v) => v.len() as u64,
            ByteView::Raw(rv) => rt_array_len(*rv).max(0) as u64,
            ByteView::Empty => 0,
        }
    }

    fn at(&self, idx: u64) -> u64 {
        if idx >= self.len() {
            return 0;
        }
        match self {
            ByteView::Packed(v) => u64::from(v[idx as usize]),
            ByteView::Values(v) => (value_byte(&v[idx as usize]) & 0xFF) as u64,
            ByteView::Raw(rv) => (rt_array_get(*rv, idx as i64).to_raw() & 0xFF) as u64,
            ByteView::Empty => 0,
        }
    }

    fn u16(&self, off: u64) -> u64 {
        self.at(off) | (self.at(off.wrapping_add(1)) << 8)
    }

    fn u32(&self, off: u64) -> u64 {
        self.u16(off) | (self.u16(off.wrapping_add(2)) << 16)
    }

    fn u64(&self, off: u64) -> u64 {
        self.u32(off) | (self.u32(off.wrapping_add(4)) << 32)
    }
}

fn value_byte(value: &Value) -> i64 {
    match value.clone().deref_pointer() {
        Value::Int(n) => n,
        Value::UInt { value, .. } => value as i64,
        Value::Union { inner, .. } => value_byte(&inner),
        other => other.as_int().unwrap_or(0),
    }
}

fn arg<'a>(args: &'a [Value], index: usize, name: &str, arity: usize) -> Result<&'a Value, CompileError> {
    args.get(index).ok_or_else(|| {
        CompileError::semantic_with_context(
            format!("{name} expects {arity} argument(s)"),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })
}

fn int_arg(args: &[Value], index: usize, name: &str, arity: usize) -> Result<u64, CompileError> {
    Ok(arg(args, index, name, arity)?.as_int()? as u64)
}

fn uint(value: u64) -> Value {
    Value::Int(value as i64)
}

/// Build a byte array of the same storage kind as `source` (packed stays packed).
fn byte_result(source: &Value, bytes: Vec<u8>) -> Value {
    match source {
        Value::ByteArray(_) | Value::FrozenByteArray(_) => Value::byte_array(bytes),
        _ => Value::array(bytes.into_iter().map(|b| Value::Int(i64::from(b))).collect()),
    }
}

pub fn rt_arm_array_len_u32_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = arg(args, 0, "rt_arm_array_len_u32", 1)?;
    Ok(uint(ByteView::of(arr).len()))
}

pub fn rt_arm_array_get_byte_u32_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = arg(args, 0, "rt_arm_array_get_byte_u32", 2)?;
    let idx = int_arg(args, 1, "rt_arm_array_get_byte_u32", 2)?;
    Ok(uint(ByteView::of(arr).at(idx)))
}

pub fn rt_arm_array_clone_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = arg(args, 0, "rt_arm_array_clone_bytes", 1)?;
    let view = ByteView::of(arr);
    let bytes = (0..view.len()).map(|i| view.at(i) as u8).collect();
    Ok(byte_result(arr, bytes))
}

pub fn rt_arm_array_slice_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = arg(args, 0, "rt_arm_array_slice_bytes", 3)?;
    let view = ByteView::of(arr);
    let len = view.len();
    let offset = int_arg(args, 1, "rt_arm_array_slice_bytes", 3)?.min(len);
    let size = int_arg(args, 2, "rt_arm_array_slice_bytes", 3)?.min(len - offset);
    let bytes = (0..size).map(|i| view.at(offset + i) as u8).collect();
    Ok(byte_result(arr, bytes))
}

fn elf64_header_ok(v: &ByteView) -> bool {
    let len = v.len();
    if len < 64 {
        return false;
    }
    if v.at(0) != 0x7F || v.at(1) != 0x45 || v.at(2) != 0x4C || v.at(3) != 0x46 {
        return false;
    }
    if v.at(4) != 2 || v.at(5) != 1 {
        return false;
    }
    if v.u16(18) != 183 || v.u16(52) != 64 || v.u16(54) != 56 {
        return false;
    }
    let phoff = v.u64(32);
    let phnum = v.u16(56);
    phoff <= len && phnum <= 256 && phoff.checked_add(phnum * 56).is_some_and(|end| end <= len)
}

fn elf64_load_phoff(v: &ByteView, wanted: u32) -> Option<u64> {
    if !elf64_header_ok(v) {
        return None;
    }
    let phoff = v.u64(32);
    let phnum = v.u16(56);
    let mut seen = 0u32;
    for idx in 0..phnum {
        let off = phoff + idx * 56;
        if v.u32(off) == 1 {
            if seen == wanted {
                return Some(off);
            }
            seen += 1;
        }
    }
    None
}

pub fn rt_arm_elf64_pt_load_count_fn(args: &[Value]) -> Result<Value, CompileError> {
    let view = ByteView::of(arg(args, 0, "rt_arm_elf64_pt_load_count", 1)?);
    if !elf64_header_ok(&view) {
        return Ok(uint(0));
    }
    let phoff = view.u64(32);
    let count = (0..view.u16(56)).filter(|idx| view.u32(phoff + idx * 56) == 1).count();
    Ok(uint(count as u64))
}

pub fn rt_arm_elf64_entry_fn(args: &[Value]) -> Result<Value, CompileError> {
    let view = ByteView::of(arg(args, 0, "rt_arm_elf64_entry", 1)?);
    Ok(uint(if elf64_header_ok(&view) { view.u64(24) } else { 0 }))
}

fn pt_load_field(args: &[Value], name: &str, field: u64, wide: bool) -> Result<Value, CompileError> {
    let view = ByteView::of(arg(args, 0, name, 2)?);
    let idx = int_arg(args, 1, name, 2)? as u32;
    Ok(uint(match elf64_load_phoff(&view, idx) {
        Some(ph) if wide => view.u64(ph + field),
        Some(ph) => view.u32(ph + field),
        None => 0,
    }))
}

pub fn rt_arm_elf64_pt_load_flags_fn(args: &[Value]) -> Result<Value, CompileError> {
    pt_load_field(args, "rt_arm_elf64_pt_load_flags", 4, false)
}

pub fn rt_arm_elf64_pt_load_offset_fn(args: &[Value]) -> Result<Value, CompileError> {
    pt_load_field(args, "rt_arm_elf64_pt_load_offset", 8, true)
}

pub fn rt_arm_elf64_pt_load_vaddr_fn(args: &[Value]) -> Result<Value, CompileError> {
    pt_load_field(args, "rt_arm_elf64_pt_load_vaddr", 16, true)
}

pub fn rt_arm_elf64_pt_load_filesz_fn(args: &[Value]) -> Result<Value, CompileError> {
    pt_load_field(args, "rt_arm_elf64_pt_load_filesz", 32, true)
}

pub fn rt_arm_elf64_pt_load_memsz_fn(args: &[Value]) -> Result<Value, CompileError> {
    pt_load_field(args, "rt_arm_elf64_pt_load_memsz", 40, true)
}

pub fn rt_arm_elf64_pt_load_align_fn(args: &[Value]) -> Result<Value, CompileError> {
    pt_load_field(args, "rt_arm_elf64_pt_load_align", 48, true)
}

/// SMF-wrapped ELF: returns the ELF stub size recorded in the 128-byte trailer.
pub fn rt_arm_smf_elf_stub_size_fn(args: &[Value]) -> Result<Value, CompileError> {
    let view = ByteView::of(arg(args, 0, "rt_arm_smf_elf_stub_size", 1)?);
    let len = view.len();
    if len < 132 || view.at(0) != 0x7F || view.at(1) != 0x45 || view.at(2) != 0x4C || view.at(3) != 0x46 {
        return Ok(uint(0));
    }
    let trailer = len - 128;
    if view.at(trailer) != 0x53
        || view.at(trailer + 1) != 0x4D
        || view.at(trailer + 2) != 0x46
        || view.at(trailer + 3) != 0
    {
        return Ok(uint(0));
    }
    let stub_size = view.u32(trailer + 52);
    Ok(uint(if stub_size > 0 && stub_size <= trailer {
        stub_size
    } else {
        trailer
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn push_le(buf: &mut Vec<u8>, value: u64, width: usize) {
        for i in 0..width {
            buf.push((value >> (i * 8)) as u8);
        }
    }

    /// One PT_LOAD aarch64 ELF64 (same shape the bare-metal header check accepts).
    fn aarch64_elf(machine: u64) -> Vec<u8> {
        let mut b = vec![0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0];
        b.resize(16, 0);
        push_le(&mut b, 2, 2);
        push_le(&mut b, machine, 2);
        push_le(&mut b, 1, 4);
        push_le(&mut b, 0x400078, 8); // entry
        push_le(&mut b, 64, 8); // phoff
        push_le(&mut b, 0, 8);
        push_le(&mut b, 0, 4);
        push_le(&mut b, 64, 2);
        push_le(&mut b, 56, 2);
        push_le(&mut b, 2, 2); // phnum: one PT_NOTE, one PT_LOAD
        push_le(&mut b, 0, 6);
        // PT_NOTE (skipped by the PT_LOAD index)
        push_le(&mut b, 4, 4);
        b.resize(64 + 56, 0);
        push_le(&mut b, 1, 4);
        push_le(&mut b, 5, 4);
        push_le(&mut b, 0x78, 8);
        push_le(&mut b, 0x400078, 8);
        push_le(&mut b, 0x400078, 8);
        push_le(&mut b, 4, 8);
        push_le(&mut b, 8, 8);
        push_le(&mut b, 0x1000, 8);
        b
    }

    fn call(f: fn(&[Value]) -> Result<Value, CompileError>, args: &[Value]) -> i64 {
        f(args).unwrap().as_int().unwrap()
    }

    #[test]
    fn byte_reads_match_bare_metal_bounds_semantics_for_both_layouts() {
        for arr in [
            Value::byte_array(vec![7, 0, 255]),
            Value::array(vec![Value::Int(7), Value::Int(0), Value::Int(255)]),
        ] {
            assert_eq!(call(rt_arm_array_len_u32_fn, &[arr.clone()]), 3);
            assert_eq!(call(rt_arm_array_get_byte_u32_fn, &[arr.clone(), Value::Int(2)]), 255);
            assert_eq!(call(rt_arm_array_get_byte_u32_fn, &[arr.clone(), Value::Int(3)]), 0);
            assert_eq!(call(rt_arm_array_get_byte_u32_fn, &[arr.clone(), Value::Int(-1)]), 0);
        }
    }

    #[test]
    fn clone_and_slice_clamp_and_keep_storage_kind() {
        let packed = Value::byte_array(vec![1, 2, 3, 4]);
        let cloned = rt_arm_array_clone_bytes_fn(&[packed.clone()]).unwrap();
        assert_eq!(cloned.byte_array_view(), Some(&[1u8, 2, 3, 4][..]));
        let sliced = rt_arm_array_slice_bytes_fn(&[packed.clone(), Value::Int(2), Value::Int(9)]).unwrap();
        assert_eq!(sliced.byte_array_view(), Some(&[3u8, 4][..]));
        let past_end = rt_arm_array_slice_bytes_fn(&[packed, Value::Int(9), Value::Int(1)]).unwrap();
        assert_eq!(past_end.byte_array_view(), Some(&[][..]));
        let boxed = Value::array(vec![Value::Int(9), Value::Int(8)]);
        match rt_arm_array_slice_bytes_fn(&[boxed, Value::Int(1), Value::Int(1)]).unwrap() {
            Value::Array(items) => assert_eq!(items.as_slice(), &[Value::Int(8)]),
            other => panic!("expected boxed array, got {}", other.type_name()),
        }
    }

    #[test]
    fn elf64_pt_load_fields_skip_non_load_headers() {
        let elf = Value::byte_array(aarch64_elf(183));
        let at = |f: fn(&[Value]) -> Result<Value, CompileError>| call(f, &[elf.clone(), Value::Int(0)]);
        assert_eq!(call(rt_arm_elf64_pt_load_count_fn, &[elf.clone()]), 1);
        assert_eq!(call(rt_arm_elf64_entry_fn, &[elf.clone()]), 0x400078);
        assert_eq!(at(rt_arm_elf64_pt_load_flags_fn), 5);
        assert_eq!(at(rt_arm_elf64_pt_load_offset_fn), 0x78);
        assert_eq!(at(rt_arm_elf64_pt_load_vaddr_fn), 0x400078);
        assert_eq!(at(rt_arm_elf64_pt_load_filesz_fn), 4);
        assert_eq!(at(rt_arm_elf64_pt_load_memsz_fn), 8);
        assert_eq!(at(rt_arm_elf64_pt_load_align_fn), 0x1000);
        assert_eq!(call(rt_arm_elf64_pt_load_vaddr_fn, &[elf, Value::Int(1)]), 0);
    }

    #[test]
    fn elf64_rejects_non_aarch64_machine_like_bare_metal() {
        let x86 = Value::byte_array(aarch64_elf(62));
        assert_eq!(call(rt_arm_elf64_pt_load_count_fn, &[x86.clone()]), 0);
        assert_eq!(call(rt_arm_elf64_entry_fn, &[x86]), 0);
    }

    #[test]
    fn smf_stub_size_reads_trailer() {
        let mut bytes = aarch64_elf(183);
        let stub = bytes.len() as u64;
        let mut trailer = vec![0x53, 0x4D, 0x46, 0];
        trailer.resize(52, 0);
        push_le(&mut trailer, stub, 4);
        trailer.resize(128, 0);
        bytes.extend(trailer);
        assert_eq!(
            call(rt_arm_smf_elf_stub_size_fn, &[Value::byte_array(bytes)]),
            stub as i64
        );
        assert_eq!(
            call(rt_arm_smf_elf_stub_size_fn, &[Value::byte_array(aarch64_elf(183))]),
            0
        );
    }
}
