use tracing::{debug, error, trace, warn};

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

/// Apply relocations to loaded code with bounds checking
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
        let sym = symbols
            .symbols
            .get(reloc.symbol_index as usize)
            .ok_or_else(|| {
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

        // Resolve symbol address
        let sym_addr = if sym.binding == SymbolBinding::Local {
            base_address.wrapping_add(sym.value as usize)
        } else {
            match imports(sym_name) {
                Some(addr) => {
                    trace!(symbol = sym_name, addr = format!("{:#x}", addr), "Resolved external symbol");
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

        // Bounds check for the relocation offset
        match reloc.reloc_type {
            RelocationType::Abs64 => {
                // Abs64 needs 8 bytes
                if offset.checked_add(8).map_or(true, |end| end > code_len) {
                    let msg = format!(
                        "Relocation {} (Abs64) at offset {} exceeds code buffer size {} (needs 8 bytes)",
                        reloc_idx, offset, code_len
                    );
                    error!("{}", msg);
                    return Err(msg);
                }

                let patch_ptr = code.as_mut_ptr().wrapping_add(offset);
                let value = sym_addr.wrapping_add(reloc.addend as usize);
                trace!(
                    reloc_idx,
                    offset,
                    value = format!("{:#x}", value),
                    "Applying Abs64 relocation"
                );
                unsafe {
                    *(patch_ptr as *mut u64) = value as u64;
                }
            }

            RelocationType::Pc32 | RelocationType::Plt32 => {
                // Pc32/Plt32 needs 4 bytes
                if offset.checked_add(4).map_or(true, |end| end > code_len) {
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

                trace!(
                    reloc_idx,
                    offset,
                    value,
                    reloc_type = ?reloc.reloc_type,
                    "Applying PC-relative relocation"
                );
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::None => {
                trace!(reloc_idx, "Skipping None relocation type");
            }

            RelocationType::GotPcRel => {
                warn!(reloc_idx, "GotPcRel relocation not yet implemented, skipping");
            }
        }
    }

    debug!(applied = relocs.len(), "Relocations applied successfully");
    Ok(())
}
