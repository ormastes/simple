use super::symbol::{SymbolBinding, SymbolTable};

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfRelocation {
    pub offset: u64,
    pub symbol_index: u32,
    pub reloc_type: RelocationType,
    pub addend: i64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u32)]
pub enum RelocationType {
    None = 0,
    Abs64 = 1,
    Pc32 = 2,
    Plt32 = 3,
    GotPcRel = 4,
}

/// Apply relocations to loaded code
pub fn apply_relocations(
    code: &mut [u8],
    relocs: &[SmfRelocation],
    symbols: &SymbolTable,
    base_address: usize,
    imports: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    for reloc in relocs {
        let sym = symbols
            .symbols
            .get(reloc.symbol_index as usize)
            .ok_or_else(|| format!("Relocation references missing symbol {}", reloc.symbol_index))?;
        let sym_name = symbols.symbol_name(sym);

        // Resolve symbol address
        let sym_addr = if sym.binding == SymbolBinding::Local {
            base_address.wrapping_add(sym.value as usize)
        } else {
            imports(sym_name).ok_or_else(|| format!("Undefined symbol: {}", sym_name))?
        };

        let patch_addr = base_address.wrapping_add(reloc.offset as usize);
        let patch_ptr = code.as_mut_ptr().wrapping_add(reloc.offset as usize);

        match reloc.reloc_type {
            RelocationType::Abs64 => {
                let value = sym_addr.wrapping_add(reloc.addend as usize);
                unsafe {
                    *(patch_ptr as *mut u64) = value as u64;
                }
            }

            RelocationType::Pc32 => {
                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::Plt32 => {
                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::None | RelocationType::GotPcRel => {}
        }
    }

    Ok(())
}
