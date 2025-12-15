//! SMF (Simple Module Format) binary generation utilities.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_common::gc::GcAllocator;
use simple_common::target::Target;
use simple_loader::smf::{
    hash_name, Arch, SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolBinding, SymbolType,
    SECTION_FLAG_EXEC, SECTION_FLAG_READ, SMF_FLAG_EXECUTABLE, SMF_MAGIC,
};

use crate::elf_utils::extract_code_from_object;

/// Write an SMF binary that returns the given value from main.
#[allow(dead_code)]
pub(crate) fn write_smf_with_return_value(
    path: &Path,
    return_value: i32,
    gc: Option<&Arc<dyn GcAllocator>>,
) -> std::io::Result<()> {
    let buf = generate_smf_bytes(return_value, gc);
    fs::write(path, buf)
}

/// Generate SMF bytes in memory that returns the given value from main.
pub fn generate_smf_bytes(return_value: i32, gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    // Generate x86-64 code to return the value
    // mov eax, imm32 = B8 + 4 bytes (little-endian)
    // ret = C3
    let code_bytes = {
        let mut code = Vec::with_capacity(6);
        code.push(0xB8u8); // mov eax, imm32
        code.extend_from_slice(&return_value.to_le_bytes());
        code.push(0xC3); // ret
        code
    };
    build_smf_with_code(&code_bytes, gc)
}

/// Build an SMF module with the given code bytes and a main symbol.
fn build_smf_with_code(code_bytes: &[u8], gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;

    if let Some(gc) = gc {
        let _ = gc.alloc_bytes(code_bytes);
    }
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: simple_loader::smf::Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut sec_name = [0u8; 16];
    sec_name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: sec_name,
    };

    let string_table = b"main\0".to_vec();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    buf
}

/// Build an SMF module with the given code bytes for a specific target architecture.
fn build_smf_with_code_for_target(
    code_bytes: &[u8],
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;

    if let Some(gc) = gc {
        let _ = gc.alloc_bytes(code_bytes);
    }
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: simple_loader::smf::Platform::from_target_os(target.os) as u8,
        arch: Arch::from_target_arch(target.arch) as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut sec_name = [0u8; 16];
    sec_name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: sec_name,
    };

    let string_table = b"main\0".to_vec();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    buf
}

/// Generate SMF bytes for a given return value and target architecture.
///
/// This generates architecture-specific code that returns the given value.
pub fn generate_smf_bytes_for_target(
    return_value: i32,
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    use simple_common::target::TargetArch;

    let code_bytes = match target.arch {
        TargetArch::X86_64 => {
            // x86-64: mov eax, imm32; ret
            let mut code = Vec::with_capacity(6);
            code.push(0xB8u8); // mov eax, imm32
            code.extend_from_slice(&return_value.to_le_bytes());
            code.push(0xC3); // ret
            code
        }
        TargetArch::X86 => {
            // i686 (32-bit x86): mov eax, imm32; ret
            // Same instruction encoding as x86-64 for simple return values
            let mut code = Vec::with_capacity(6);
            code.push(0xB8u8); // mov eax, imm32
            code.extend_from_slice(&return_value.to_le_bytes());
            code.push(0xC3); // ret
            code
        }
        TargetArch::Aarch64 => {
            // ARM64: mov w0, #imm; ret
            // Note: ARM64 has complex immediate encoding; for simplicity use movz + movk
            let mut code = Vec::new();
            let val = return_value as u32;
            let low16 = val & 0xFFFF;
            let high16 = (val >> 16) & 0xFFFF;

            // movz w0, #low16
            let movz = 0x52800000u32 | ((low16 as u32) << 5);
            code.extend_from_slice(&movz.to_le_bytes());

            if high16 != 0 {
                // movk w0, #high16, lsl #16
                let movk = 0x72A00000u32 | ((high16 as u32) << 5);
                code.extend_from_slice(&movk.to_le_bytes());
            }

            // ret
            code.extend_from_slice(&0xD65F03C0u32.to_le_bytes());
            code
        }
        TargetArch::Arm => {
            // ARM32: mov r0, #imm; bx lr
            // Simplified - only handles small values
            let mut code = Vec::new();
            // mov r0, #value (simplified - requires value in 8-bit range with rotation)
            // For full support, would need multiple instructions
            let val = return_value as u32;
            // e3a00000 + imm8 = mov r0, #imm8
            let mov = 0xE3A00000u32 | (val & 0xFF);
            code.extend_from_slice(&mov.to_le_bytes());
            // bx lr
            code.extend_from_slice(&0xE12FFF1Eu32.to_le_bytes());
            code
        }
        TargetArch::Riscv64 | TargetArch::Riscv32 => {
            // RISC-V: li a0, imm; ret
            let mut code = Vec::new();
            let val = return_value as i32;

            if val >= -2048 && val < 2048 {
                // addi a0, zero, imm (I-type)
                let addi = 0x00000513u32 | (((val as u32) & 0xFFF) << 20);
                code.extend_from_slice(&addi.to_le_bytes());
            } else {
                // lui a0, hi20; addi a0, a0, lo12
                let hi20 = ((val as u32).wrapping_add(0x800) >> 12) & 0xFFFFF;
                let lo12 = (val as u32) & 0xFFF;
                let lui = 0x00000537u32 | (hi20 << 12);
                let addi = 0x00050513u32 | (lo12 << 20);
                code.extend_from_slice(&lui.to_le_bytes());
                code.extend_from_slice(&addi.to_le_bytes());
            }

            // ret (jalr zero, ra, 0)
            code.extend_from_slice(&0x00008067u32.to_le_bytes());
            code
        }
    };

    build_smf_with_code_for_target(&code_bytes, gc, target)
}

/// Generate SMF from Cranelift object code for a specific target.
pub fn generate_smf_from_object_for_target(
    object_code: &[u8],
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    let code_bytes = extract_code_from_object(object_code);
    build_smf_with_code_for_target(&code_bytes, gc, target)
}

/// Generate SMF from Cranelift object code (using current host target).
pub fn generate_smf_from_object(object_code: &[u8], gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    let code_bytes = extract_code_from_object(object_code);
    build_smf_with_code(&code_bytes, gc)
}

/// Helper to write a struct to a byte buffer.
fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let bytes = unsafe {
        std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>())
    };
    buf.extend_from_slice(bytes);
}
