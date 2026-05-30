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
    Arm64Branch26 = 5,
    Arm64Page21 = 6,
    Arm64PageOff12 = 7,
    Arm64GotLoadPage21 = 8,
    Arm64GotLoadPageOff12 = 9,
}

pub fn apply_relocations(
    code: &mut [u8],
    relocs: &[SmfRelocation],
    symbols: &SymbolTable,
    base_address: usize,
    imports: &dyn Fn(&str) -> Option<usize>,
    got_slot_resolver: &mut dyn FnMut(u32, usize) -> Result<usize, String>,
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

        let sym_addr = if sym.visibility != 0 || sym.binding == SymbolBinding::Local || sym.value != 0 || sym.size != 0
        {
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

        let got_slot = if matches!(
            reloc.reloc_type,
            RelocationType::GotPcRel | RelocationType::Arm64GotLoadPage21 | RelocationType::Arm64GotLoadPageOff12
        ) {
            got_slot_resolver(reloc.symbol_index, sym_addr)?
        } else {
            0
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
            RelocationType::Arm64Branch26 => {
                if offset.checked_add(4).is_none_or(|end| end > code_len) {
                    let msg = format!(
                        "Relocation {} (Arm64Branch26) at offset {} exceeds code buffer size {} (needs 4 bytes)",
                        reloc_idx, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let patch_addr = base_address.wrapping_add(offset);
                let target = (sym_addr as i64).wrapping_add(reloc.addend);
                let diff = target.wrapping_sub(patch_addr as i64);
                let shifted = diff >> 2;
                if !((shifted >> 26 == -1) || (shifted >> 26 == 0)) {
                    let msg = format!(
                        "Arm64Branch26 relocation {} target out of range: patch={:#x} target={:#x} diff={:#x}",
                        reloc_idx, patch_addr, target, diff
                    );
                    error!("{}", msg);
                    return Err(msg);
                }
                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                unsafe {
                    let inst = std::ptr::read_unaligned(patch_ptr as *const u32);
                    let imm26 = (shifted as u32) & 0x03ff_ffff;
                    std::ptr::write_unaligned(patch_ptr as *mut u32, (inst & 0xfc00_0000) | imm26);
                }
            }
            RelocationType::Arm64Page21 | RelocationType::Arm64GotLoadPage21 => {
                if offset.checked_add(4).is_none_or(|end| end > code_len) {
                    let msg = format!(
                        "Relocation {} ({:?}) at offset {} exceeds code buffer size {} (needs 4 bytes)",
                        reloc_idx, reloc.reloc_type, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let target_base = if reloc.reloc_type == RelocationType::Arm64GotLoadPage21 {
                    got_slot
                } else {
                    sym_addr
                };
                let target = (target_base as i64).wrapping_add(reloc.addend) as usize;
                let patch_addr = base_address.wrapping_add(offset);
                let target_page = target & !0xfffusize;
                let patch_page = patch_addr & !0xfffusize;
                let page_delta = ((target_page as i64).wrapping_sub(patch_page as i64)) >> 12;
                if !((page_delta >> 20 == -1) || (page_delta >> 20 == 0)) {
                    let msg = format!(
                        "Arm64Page21 relocation {} target out of range: patch={:#x} target={:#x} delta_pages={:#x}",
                        reloc_idx, patch_addr, target, page_delta
                    );
                    error!("{}", msg);
                    return Err(msg);
                }
                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                unsafe {
                    let inst = std::ptr::read_unaligned(patch_ptr as *const u32);
                    let immlo = ((page_delta as u32) & 0x3) << 29;
                    let immhi = (((page_delta as u32) >> 2) & 0x7ffff) << 5;
                    let mask = !((0x7ffff << 5) | (0x3 << 29));
                    std::ptr::write_unaligned(patch_ptr as *mut u32, (inst & mask) | immlo | immhi);
                }
            }
            RelocationType::Arm64PageOff12 | RelocationType::Arm64GotLoadPageOff12 => {
                if offset.checked_add(4).is_none_or(|end| end > code_len) {
                    let msg = format!(
                        "Relocation {} ({:?}) at offset {} exceeds code buffer size {} (needs 4 bytes)",
                        reloc_idx, reloc.reloc_type, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let target_base = if reloc.reloc_type == RelocationType::Arm64GotLoadPageOff12 {
                    got_slot
                } else {
                    sym_addr
                };
                let target = (target_base as i64).wrapping_add(reloc.addend) as usize;
                let pageoff = target & 0xfffusize;
                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                unsafe {
                    let inst = std::ptr::read_unaligned(patch_ptr as *const u32);
                    // ADD/SUB (immediate) encode an unscaled 12-bit immediate at bits 21:10.
                    let is_add_sub_imm = (inst & 0x1f00_0000) == 0x1100_0000;
                    let imm12 = if is_add_sub_imm {
                        pageoff as u32
                    } else {
                        // LDR/STR unsigned immediates encode pageoff scaled by access size.
                        let scale = ((inst >> 30) & 0x3) as usize;
                        (pageoff >> scale) as u32
                    } & 0x0fff;
                    let mask = !(0x0fff << 10);
                    std::ptr::write_unaligned(patch_ptr as *mut u32, (inst & mask) | (imm12 << 10));
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

        apply_relocations(
            &mut code,
            &relocs,
            &symbols,
            base_address,
            &|_| {
                import_lookups.set(import_lookups.get() + 1);
                None
            },
            &mut |_sym, _addr| Err("unexpected GOT relocation".to_string()),
        )
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

        apply_relocations(
            &mut code,
            &relocs,
            &symbols,
            base_address,
            &|_| {
                import_lookups.set(import_lookups.get() + 1);
                None
            },
            &mut |_sym, _addr| Err("unexpected GOT relocation".to_string()),
        )
        .expect("defined globals at offset zero should relocate from the module body");

        assert_eq!(import_lookups.get(), 0);
        assert_eq!(u64::from_le_bytes(code), base_address as u64);
    }
}
