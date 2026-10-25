//! ABI 1: target-owned readonly words with at most one data relocation.
use super::*;

/// The caller lends initialized, readable name bytes and native i64 words for
/// this call only. No host pointer is retained in the emitted data. Zero is a
/// rejected request. A backend definition failure retires the module, because
/// Cranelift has no undeclare operation; a partial artifact cannot be emitted.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_declare_readonly_words_v1(
    module: i64,
    name_ptr: i64,
    name_len: i64,
    words_ptr: i64,
    word_count: i64,
    alignment: i64,
    reloc_word_index: i64,
    reloc_target_data_id: i64,
    reloc_addend: i64,
) -> i64 {
    let Some(name_size) = checked_span(name_ptr, name_len) else {
        return 0;
    };
    let Some(byte_count) = word_count.checked_mul(8) else {
        return 0;
    };
    let Some(byte_size) = checked_span(words_ptr, byte_count) else {
        return 0;
    };
    if alignment < 8
        || !(alignment as u64).is_power_of_two()
        || alignment as u64 > CL_STATIC_MAX_ALIGNMENT
        || reloc_addend != 0
        || reloc_word_index < -1
        || reloc_word_index >= word_count
        || (reloc_word_index == -1 && reloc_target_data_id != 0)
    {
        return 0;
    }
    let name_bytes = std::slice::from_raw_parts(name_ptr as *const u8, name_size);
    let Ok(name) = std::str::from_utf8(name_bytes) else {
        return 0;
    };
    if name.contains('\0') {
        return 0;
    }
    let mut bytes = Vec::new();
    if bytes.try_reserve_exact(byte_size).is_err() {
        return 0;
    }
    for index in 0..word_count as usize {
        let word = std::ptr::read_unaligned((words_ptr as *const u8).add(index * 8).cast::<i64>());
        if index as i64 == reloc_word_index && word != 0 {
            return 0;
        }
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    let mut jit = JIT_MODULES.lock().unwrap();
    if let Some(ctx) = jit.get_mut(&module) {
        let result = define_words(
            &mut ctx.module,
            &mut ctx.readonly_words_v1,
            name,
            bytes,
            alignment as u64,
            reloc_word_index,
            reloc_target_data_id,
        );
        if let Ok(handle) = result {
            ctx.exposed_handles.push((false, handle));
        }
        drop(jit);
        if matches!(result, Err(true)) {
            rt_cranelift_free_module(module);
        }
        return result.unwrap_or(0);
    }
    drop(jit);
    let mut aot = AOT_MODULES.lock().unwrap();
    let Some(ctx) = aot.get_mut(&module) else { return 0 };
    let result = define_words(
        &mut ctx.module,
        &mut ctx.readonly_words_v1,
        name,
        bytes,
        alignment as u64,
        reloc_word_index,
        reloc_target_data_id,
    );
    if let Ok(handle) = result {
        ctx.exposed_handles.push((false, handle));
    }
    drop(aot);
    if matches!(result, Err(true)) {
        rt_cranelift_free_module(module);
    }
    result.unwrap_or(0)
}

fn checked_span(pointer: i64, length: i64) -> Option<usize> {
    if pointer == 0 || length <= 0 {
        return None;
    }
    let size = usize::try_from(length).ok()?;
    if size > isize::MAX as usize {
        return None;
    }
    (pointer as usize).checked_add(size)?;
    Some(size)
}

// Err(false) is validation rejection; Err(true) requires retiring the module.
fn define_words<M: Module>(
    module: &mut M,
    registry: &mut HashMap<i64, (DataId, usize)>,
    name: &str,
    bytes: Vec<u8>,
    alignment: u64,
    reloc_index: i64,
    target: i64,
) -> Result<i64, bool> {
    if module.target_config().pointer_type().bytes() != 8
        || module.isa().endianness() != cranelift_codegen::ir::Endianness::Little
        || module.get_name(name).is_some()
    {
        return Err(false);
    }
    let target_id = if reloc_index >= 0 {
        let Some(&(id, extent)) = registry.get(&target) else {
            return Err(false);
        };
        if extent == 0 {
            return Err(false);
        }
        Some(id)
    } else {
        None
    };
    let size = bytes.len();
    let mut desc = DataDescription::new();
    desc.set_align(alignment);
    desc.define(bytes.into_boxed_slice());
    if let Some(target_id) = target_id {
        let offset = u32::try_from(reloc_index.checked_mul(8).ok_or(false)?).map_err(|_| false)?;
        let reference = module.declare_data_in_data(target_id, &mut desc);
        desc.write_data_addr(offset, reference, 0);
    }
    let id = module
        .declare_data(name, Linkage::Local, false, false)
        .map_err(|_| false)?;
    module.define_data(id, &desc).map_err(|_| true)?;
    let handle = next_handle();
    registry.insert(handle, (id, size));
    DECLARED_DATA.lock().unwrap().insert(handle, id);
    Ok(handle)
}

#[cfg(all(test, any(target_arch = "x86_64", target_arch = "aarch64"), target_os = "linux"))]
mod tests {
    use super::*;
    use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SectionKind};

    unsafe fn declare(
        module: i64,
        name: &str,
        words: &[i64],
        alignment: i64,
        index: i64,
        target: i64,
        addend: i64,
    ) -> i64 {
        rt_cranelift_declare_readonly_words_v1(
            module,
            name.as_ptr() as i64,
            name.len() as i64,
            words.as_ptr() as i64,
            words.len() as i64,
            alignment,
            index,
            target,
            addend,
        )
    }

    #[test]
    fn readonly_words_v1_object_relocation_link_and_rejections() {
        unsafe {
            let target = if cfg!(target_arch = "aarch64") {
                CL_TARGET_AARCH64
            } else {
                CL_TARGET_X86_64
            };
            let module = rt_cranelift_new_aot_module(b"rodata".as_ptr() as i64, 6, target);
            assert!(module > 0);
            let slots = declare(module, "c4_slots", &[37, 2, 8, 0], 8, -1, 0, 0);
            assert!(slots > 0);
            // Invalid requests leave the name available for the following valid declaration.
            for (alignment, index, target, addend) in [
                (3, 4, slots, 0),
                (8, 6, slots, 0),
                (8, 4, i64::MAX, 0),
                (8, 4, slots, 1),
                (8, -2, 0, 0),
                (8, -1, slots, 0),
            ] {
                assert_eq!(
                    declare(
                        module,
                        "c4_header",
                        &[1, 6, 4, 1, 0, 0],
                        alignment,
                        index,
                        target,
                        addend
                    ),
                    0
                );
            }
            assert_eq!(declare(module, "c4_header", &[1, 6, 4, 1, 99, 0], 8, 4, slots, 0), 0);
            let other = rt_cranelift_new_aot_module(b"other".as_ptr() as i64, 5, target);
            assert_eq!(declare(other, "bad_owner", &[0], 8, 0, slots, 0), 0);
            rt_cranelift_free_module(other);
            let header = declare(module, "c4_header", &[1, 6, 4, 1, 0, 0], 8, 4, slots, 0);
            assert!(header > 0);
            assert_eq!(declare(module, "c4_header", &[0], 8, -1, 0, 0), 0);
            let signature = rt_cranelift_new_signature(0);
            rt_cranelift_sig_set_return(signature, 4);
            let ctx = rt_cranelift_begin_function(module, b"read_c4".as_ptr() as i64, 7, signature);
            let block = rt_cranelift_create_block(ctx);
            rt_cranelift_switch_to_block(ctx, block);
            rt_cranelift_seal_block(ctx, block);
            let address = rt_cranelift_data_addr_in_func(ctx, header);
            let pointer = rt_cranelift_load(ctx, 4, address, 32);
            let value = rt_cranelift_load(ctx, 4, pointer, 0);
            rt_cranelift_return(ctx, value);
            let finished = rt_cranelift_end_function(ctx);
            assert!(rt_cranelift_aot_define_function(
                module,
                b"read_c4".as_ptr() as i64,
                7,
                finished
            ));
            let getter = rt_cranelift_begin_function(module, b"get_c4".as_ptr() as i64, 6, signature);
            let block = rt_cranelift_create_block(getter);
            rt_cranelift_switch_to_block(getter, block);
            rt_cranelift_seal_block(getter, block);
            let pointer = rt_cranelift_data_addr_in_func(getter, header);
            rt_cranelift_return(getter, pointer);
            let finished = rt_cranelift_end_function(getter);
            assert!(rt_cranelift_aot_define_function(
                module,
                b"get_c4".as_ptr() as i64,
                6,
                finished
            ));
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("descriptor.o");
            let path_text = path.to_str().unwrap();
            assert!(rt_cranelift_emit_object_raw(
                module,
                path_text.as_ptr() as i64,
                path_text.len() as i64
            ));
            let bytes = std::fs::read(&path).unwrap();
            let object = object::File::parse(bytes.as_slice()).unwrap();
            let slots_symbol = object.symbol_by_name("c4_slots").unwrap();
            let header_symbol = object.symbol_by_name("c4_header").unwrap();
            let section = object.section_by_index(header_symbol.section_index().unwrap()).unwrap();
            // Cranelift uses ELF .data.rel.ro for readonly data containing relocations.
            assert!(section.name().unwrap().starts_with(".data.rel.ro"));
            assert!(section.align() >= 8);
            let offset = header_symbol.address() - section.address();
            assert_eq!(
                &section.data().unwrap()[offset as usize + 32..offset as usize + 40],
                &[0; 8]
            );
            let (_, relocation) = section.relocations().find(|(at, _)| *at == offset + 32).unwrap();
            assert_eq!(relocation.size(), 64);
            assert_eq!(relocation.addend(), 0);
            assert_eq!(relocation.target(), RelocationTarget::Symbol(slots_symbol.index()));
            let slots_section = object.section_by_index(slots_symbol.section_index().unwrap()).unwrap();
            assert_eq!(slots_section.kind(), SectionKind::ReadOnlyData);
            assert_eq!(&slots_section.data().unwrap()[..8], &37_i64.to_le_bytes());
            let main = dir.path().join("main.c");
            std::fs::write(
                &main,
                "extern long read_c4(void); extern long* get_c4(void); int main(int argc, char** argv) { if (argc > 1) { ((volatile long*)get_c4())[0] = 2; return 3; } return read_c4() == 37 ? 0 : 1; }\n",
            )
            .unwrap();
            let executable = dir.path().join("read_c4");
            let output = std::process::Command::new("cc")
                .arg("-fuse-ld=bfd").arg("-no-pie")
                .arg("-Wl,-z,relro,-z,now")
                .arg(&main)
                .arg(&path)
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
            assert!(std::process::Command::new(&executable).status().unwrap().success());
            use std::os::unix::process::ExitStatusExt;
            let write = std::process::Command::new(&executable).arg("write").status().unwrap();
            assert_eq!(write.signal(), Some(11), "linked RELRO descriptor must reject writes");
            rt_cranelift_free_module(module);
            assert!(!DECLARED_DATA.lock().unwrap().contains_key(&header));
            assert!(!DECLARED_DATA.lock().unwrap().contains_key(&slots));
            assert_eq!(declare(module, "dead", &[1], 8, -1, 0, 0), 0);
        }
    }
}
