use super::symbol::{SymbolBinding, SymbolTable};

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfRelocation {
    pub offset: u64,
    pub symbol_index: u32,
    pub reloc_type: RelocationType,
    pub addend: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum RelocationType {
    None = 0,
    Abs64 = 1,
    /// PC-relative 32-bit relocation (also known as Rel32)
    Pc32 = 2,
    Plt32 = 3,
    GotPcRel = 4,
}

/// Apply relocations to loaded code.
///
/// All pointer writes are bounds-checked against the code slice length
/// before performing any unsafe write operations.
pub fn apply_relocations(
    code: &mut [u8],
    relocs: &[SmfRelocation],
    symbols: &SymbolTable,
    base_address: usize,
    imports: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let code_len = code.len();

    for reloc in relocs {
        let sym = symbols
            .symbols
            .get(reloc.symbol_index as usize)
            .ok_or_else(|| {
                format!(
                    "Relocation references missing symbol {}",
                    reloc.symbol_index
                )
            })?;
        let sym_name = symbols.symbol_name(sym);

        // Resolve symbol address
        let sym_addr = if sym.binding == SymbolBinding::Local {
            base_address.wrapping_add(sym.value as usize)
        } else {
            imports(sym_name).ok_or_else(|| format!("Undefined symbol: {}", sym_name))?
        };

        let reloc_offset = reloc.offset as usize;
        let patch_addr = base_address.wrapping_add(reloc_offset);

        match reloc.reloc_type {
            RelocationType::Abs64 => {
                // Bounds check: need 8 bytes at reloc_offset for u64 write
                if reloc_offset.checked_add(std::mem::size_of::<u64>()).map_or(true, |end| end > code_len) {
                    return Err(format!(
                        "Abs64 relocation at offset {} overflows code buffer (len {})",
                        reloc_offset, code_len
                    ));
                }

                let value = sym_addr.wrapping_add(reloc.addend as usize);
                let patch_ptr = code.as_mut_ptr().wrapping_add(reloc_offset);
                unsafe {
                    *(patch_ptr as *mut u64) = value as u64;
                }
            }

            RelocationType::Pc32 => {
                // Bounds check: need 4 bytes at reloc_offset for i32 write
                if reloc_offset.checked_add(std::mem::size_of::<i32>()).map_or(true, |end| end > code_len) {
                    return Err(format!(
                        "Pc32 relocation at offset {} overflows code buffer (len {})",
                        reloc_offset, code_len
                    ));
                }

                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                let patch_ptr = code.as_mut_ptr().wrapping_add(reloc_offset);
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::Plt32 => {
                // Bounds check: need 4 bytes at reloc_offset for i32 write
                if reloc_offset.checked_add(std::mem::size_of::<i32>()).map_or(true, |end| end > code_len) {
                    return Err(format!(
                        "Plt32 relocation at offset {} overflows code buffer (len {})",
                        reloc_offset, code_len
                    ));
                }

                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                let patch_ptr = code.as_mut_ptr().wrapping_add(reloc_offset);
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::None | RelocationType::GotPcRel => {}
        }
    }

    Ok(())
}
