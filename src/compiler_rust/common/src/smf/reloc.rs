use tracing::{debug, error, trace};

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
    Pc32 = 2,
    Plt32 = 3,
    GotPcRel = 4,
}

pub fn apply_relocations(
    code: &mut [u8],
    relocs: &[SmfRelocation],
    symbols: &SymbolTable,
    base_address: usize,
    imports: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let code_len = code.len();
    debug!(
        code_len,
        reloc_count = relocs.len(),
        base_address = format!("{:#x}", base_address),
        "Applying relocations"
    );

    for (reloc_idx, reloc) in relocs.iter().enumerate() {
        let sym = symbols.symbols.get(reloc.symbol_index as usize).ok_or_else(|| {
            let msg = format!(
                "Relocation {} references missing symbol index {} (max: {})",
                reloc_idx,
                reloc.symbol_index,
                symbols.symbols.len()
            );
            error!("{}", msg);
            msg
        })?;
        let sym_name = symbols.symbol_name(sym);

        trace!(
            reloc_idx,
            symbol = sym_name,
            reloc_type = ?reloc.reloc_type,
            offset = reloc.offset,
            "Processing relocation"
        );

        let sym_addr = if sym.visibility != 0 || sym.binding == SymbolBinding::Local || sym.value != 0 || sym.size != 0 {
            base_address.wrapping_add(sym.value as usize)
        } else {
            match imports(sym_name) {
                Some(addr) => {
                    trace!(
                        symbol = sym_name,
                        addr = format!("{:#x}", addr),
                        "Resolved external symbol"
                    );
                    addr
                }
                None => {
                    let msg = format!("Undefined symbol: {} (required by relocation {})", sym_name, reloc_idx);
                    error!("{}", msg);
                    return Err(msg);
                }
            }
        };

        let offset = reloc.offset as usize;
        match reloc.reloc_type {
            RelocationType::Abs64 => {
                if offset.checked_add(8).is_none_or(|end| end > code_len) {
                    let msg = format!(
                        "Relocation {} (Abs64) at offset {} exceeds code buffer size {} (needs 8 bytes)",
                        reloc_idx, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                let value = sym_addr.wrapping_add(reloc.addend as usize) as u64;
                trace!(
                    reloc_idx,
                    offset,
                    value = format!("{:#x}", value),
                    "Applying Abs64 relocation"
                );
                unsafe {
                    std::ptr::write_unaligned(patch_ptr as *mut u64, value);
                }
            }
            RelocationType::Pc32 | RelocationType::Plt32 => {
                if offset.checked_add(4).is_none_or(|end| end > code_len) {
                    let msg = format!(
                        "Relocation {} ({:?}) at offset {} exceeds code buffer size {} (needs 4 bytes)",
                        reloc_idx, reloc.reloc_type, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let patch_addr = base_address.wrapping_add(offset);
                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                trace!(reloc_idx, offset, value, reloc_type = ?reloc.reloc_type, "Applying PC-relative relocation");
                unsafe {
                    std::ptr::write_unaligned(patch_ptr as *mut i32, value);
                }
            }
            RelocationType::None => {
                trace!(reloc_idx, "Skipping None relocation type");
            }
            RelocationType::GotPcRel => {
                if offset.checked_add(4).is_none_or(|end| end > code_len) {
                    let msg = format!(
                        "Relocation {} (GotPcRel) at offset {} exceeds code buffer size {} (needs 4 bytes)",
                        reloc_idx, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let got_value = sym_addr as u64;
                let got_slot = Box::leak(Box::new(got_value)) as *mut u64 as usize;
                let patch_addr = base_address.wrapping_add(offset);
                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                let value = (got_slot as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                trace!(
                    reloc_idx,
                    offset,
                    got_slot = format!("{:#x}", got_slot),
                    got_value = format!("{:#x}", got_value),
                    "Applying GOT PC-relative relocation"
                );
                unsafe {
                    std::ptr::write_unaligned(patch_ptr as *mut i32, value);
                }
            }
        }
    }

    debug!(applied = relocs.len(), "Relocations applied successfully");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    use crate::smf::symbol::{hash_name, SmfSymbol, SymbolTable, SymbolType};

    #[test]
    fn applies_defined_global_symbol_without_import_lookup() {
        let name = b"___max_i32\0".to_vec();
        let symbol = SmfSymbol {
            name_offset: 0,
            name_hash: hash_name("___max_i32"),
            sym_type: SymbolType::Function,
            binding: SymbolBinding::Global,
            visibility: 0,
            flags: 0,
            value: 0x40,
            size: 0,
            type_id: 0,
            version: 0,
            template_param_count: 0,
            reserved: [0; 3],
            template_offset: 0,
        };
        let symbols = SymbolTable::new(vec![symbol], name);
        let relocs = [SmfRelocation {
            offset: 0,
            symbol_index: 0,
            reloc_type: RelocationType::Abs64,
            addend: 0,
        }];
        let mut code = [0u8; 8];
        let base_address = 0x1000usize;
        let import_lookups = Cell::new(0);

        apply_relocations(&mut code, &relocs, &symbols, base_address, &|_| {
            import_lookups.set(import_lookups.get() + 1);
            None
        })
        .expect("defined globals should relocate from the module body");

        assert_eq!(import_lookups.get(), 0);
        assert_eq!(u64::from_le_bytes(code), (base_address + 0x40) as u64);
    }

    #[test]
    fn applies_defined_global_symbol_at_offset_zero_without_import_lookup() {
        let name = b"parse_ui_to_tree\0".to_vec();
        let symbol = SmfSymbol {
            name_offset: 0,
            name_hash: hash_name("parse_ui_to_tree"),
            sym_type: SymbolType::Function,
            binding: SymbolBinding::Global,
            visibility: 0,
            flags: 0,
            value: 0,
            size: 32,
            type_id: 0,
            version: 0,
            template_param_count: 0,
            reserved: [0; 3],
            template_offset: 0,
        };
        let symbols = SymbolTable::new(vec![symbol], name);
        let relocs = [SmfRelocation {
            offset: 0,
            symbol_index: 0,
            reloc_type: RelocationType::Abs64,
            addend: 0,
        }];
        let mut code = [0u8; 8];
        let base_address = 0x2000usize;
        let import_lookups = Cell::new(0);

        apply_relocations(&mut code, &relocs, &symbols, base_address, &|_| {
            import_lookups.set(import_lookups.get() + 1);
            None
        })
        .expect("defined globals at offset zero should relocate from the module body");

        assert_eq!(import_lookups.get(), 0);
        assert_eq!(u64::from_le_bytes(code), base_address as u64);
    }
}
