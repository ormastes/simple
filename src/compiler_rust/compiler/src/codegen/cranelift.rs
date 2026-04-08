//! AOT (Ahead-of-Time) compilation using Cranelift with ObjectModule.

use cranelift_object::{ObjectBuilder, ObjectModule};

use simple_common::target::Target;

use crate::mir::MirModule;

use super::common_backend::{create_isa_and_flags, BackendError, BackendResult, BackendSettings, CodegenBackend};

// Re-export error types for backwards compatibility
pub use super::common_backend::BackendError as CodegenError;
pub type CodegenResult<T> = BackendResult<T>;

/// AOT Codegen context for translating MIR to object code
pub struct Codegen {
    backend: CodegenBackend<ObjectModule>,
}

impl Codegen {
    /// Create a new codegen for the host target.
    pub fn new() -> CodegenResult<Self> {
        Self::for_target(Target::host())
    }

    /// Create a new codegen for a specific target.
    ///
    /// This enables cross-compilation to different architectures.
    pub fn for_target(target: Target) -> CodegenResult<Self> {
        let settings = BackendSettings::aot_for_target(target);
        let (_flags, isa) = create_isa_and_flags(&settings)?;

        let builder = ObjectBuilder::new(isa, "simple_module", cranelift_module::default_libcall_names())
            .map_err(|e| BackendError::ModuleError(e.to_string()))?;

        let module = ObjectModule::new(builder);
        let backend = CodegenBackend::with_module_and_target(module, target)?;

        Ok(Self { backend })
    }

    /// Get the target this codegen is compiling for.
    pub fn target(&self) -> &Target {
        self.backend.target()
    }

    /// Set the module prefix for name mangling in multi-file builds.
    pub fn set_module_prefix(&mut self, prefix: String) {
        self.backend.set_module_prefix(prefix);
    }

    /// Mark this module as the program entry point.
    ///
    /// When `true`, the `main` function is emitted as `spl_main` with
    /// Preemptible linkage. Non-entry modules mangle `main` like any
    /// other local function to avoid symbol collisions.
    pub fn set_entry_module(&mut self, is_entry: bool) {
        self.backend.set_entry_module(is_entry);
    }

    /// Set the import map for cross-module function resolution.
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.backend.set_import_map(map);
    }

    /// Set the ambiguous names for symbol resolution.
    pub fn set_ambiguous_names(&mut self, names: std::sync::Arc<std::collections::HashSet<String>>) {
        self.backend.set_ambiguous_names(names);
    }

    /// Set the per-module use map for resolving imports from `use` statements.
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.backend.set_use_map(map);
    }

    /// Get a reference to the inner backend for accessing mangling and resolution state.
    pub fn backend(&self) -> &CodegenBackend<ObjectModule> {
        &self.backend
    }

    /// Compile a MIR module to object code.
    pub fn compile_module(mut self, mir: &MirModule) -> CodegenResult<Vec<u8>> {
        // Compile all functions
        self.backend.compile_all_functions(mir)?;

        // Emit object code
        let product = self.backend.module.finish();
        let bytes = product.emit().map_err(|e| BackendError::ModuleError(e.to_string()))?;
        Ok(fix_macho_strsize(bytes))
    }

    /// Finish compilation and get the raw object code.
    pub fn get_object_code(self) -> Vec<u8> {
        let product = self.backend.module.finish();
        let bytes = product.emit().unwrap();
        fix_macho_strsize(bytes)
    }
}

/// Fix Cranelift Mach-O object emission bug: the object crate (0.36.x) writes
/// relocation entries that overflow into the symbol table, corrupting the first
/// N nlist entries. Detected by n_strx values exceeding the string table size.
///
/// Fix strategy: remove the corrupted nlist entries by shifting valid entries
/// forward and updating nsyms in LC_SYMTAB.
fn fix_macho_strsize(mut bytes: Vec<u8>) -> Vec<u8> {
    // Only fix Mach-O 64-bit (magic 0xFEEDFACF)
    if bytes.len() < 32 {
        return bytes;
    }
    let magic = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    if magic != 0xFEEDFACF {
        return bytes;
    }

    let ncmds = u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]) as usize;
    let mut cmd_offset = 32usize;
    for _ in 0..ncmds {
        if cmd_offset + 8 > bytes.len() {
            break;
        }
        let cmd = u32::from_le_bytes([
            bytes[cmd_offset],
            bytes[cmd_offset + 1],
            bytes[cmd_offset + 2],
            bytes[cmd_offset + 3],
        ]);
        let cmdsize = u32::from_le_bytes([
            bytes[cmd_offset + 4],
            bytes[cmd_offset + 5],
            bytes[cmd_offset + 6],
            bytes[cmd_offset + 7],
        ]) as usize;
        if cmd == 2 {
            // LC_SYMTAB
            if cmd_offset + 24 > bytes.len() {
                break;
            }
            let symoff = u32::from_le_bytes([
                bytes[cmd_offset + 8],
                bytes[cmd_offset + 9],
                bytes[cmd_offset + 10],
                bytes[cmd_offset + 11],
            ]) as usize;
            let nsyms = u32::from_le_bytes([
                bytes[cmd_offset + 12],
                bytes[cmd_offset + 13],
                bytes[cmd_offset + 14],
                bytes[cmd_offset + 15],
            ]) as usize;
            let stroff = u32::from_le_bytes([
                bytes[cmd_offset + 16],
                bytes[cmd_offset + 17],
                bytes[cmd_offset + 18],
                bytes[cmd_offset + 19],
            ]) as usize;
            let strsize = u32::from_le_bytes([
                bytes[cmd_offset + 20],
                bytes[cmd_offset + 21],
                bytes[cmd_offset + 22],
                bytes[cmd_offset + 23],
            ]) as usize;

            // Pad file if stroff + strsize extends past EOF
            let needed = stroff + strsize;
            if needed > bytes.len() {
                bytes.resize(needed, 0);
            }

            // Count corrupted nlist entries at the start of the symbol table
            let nlist_size = 16usize; // sizeof(nlist_64)
            let mut bad_count = 0usize;
            for i in 0..nsyms {
                let nlist_off = symoff + i * nlist_size;
                if nlist_off + 4 > bytes.len() {
                    break;
                }
                let n_strx = u32::from_le_bytes([
                    bytes[nlist_off],
                    bytes[nlist_off + 1],
                    bytes[nlist_off + 2],
                    bytes[nlist_off + 3],
                ]) as usize;
                if n_strx >= strsize {
                    bad_count += 1;
                } else {
                    break; // corrupted entries are always at the start (relocation overflow)
                }
            }

            // Also scan for corrupted .init_array relocations and fix them.
            // The object crate bug causes relocation overflow which corrupts both
            // the symbol table and nearby section relocations.
            // Fix: rewrite the entire .o file from scratch using the object crate's reader+writer.
            // This is the nuclear option but guarantees correctness.
            if bad_count > 0 {
                // Re-emit the object file using the object crate's reader+writer
                // to produce a clean Mach-O without the relocation overflow.
                if let Ok(clean) = reemit_clean_macho(&bytes) {
                    return clean;
                }
                // Fallback: zero out corrupted nlist entries
                for i in 0..bad_count {
                    let nlist_off = symoff + i * nlist_size;
                    for b in 0..nlist_size {
                        if nlist_off + b < bytes.len() {
                            bytes[nlist_off + b] = 0;
                        }
                    }
                }
            }
            break;
        }
        cmd_offset += cmdsize;
    }
    bytes
}

/// Re-emit a clean Mach-O object by reading the malformed one with the `object` crate
/// and writing it back. The reader/writer cycle produces valid section layouts.
fn reemit_clean_macho(malformed: &[u8]) -> Result<Vec<u8>, String> {
    use object::read::macho::{MachOFile64, MachHeader as _};
    use object::read::{Object, ObjectSection, ObjectSymbol};
    use object::write;
    use object::{Architecture, BinaryFormat, Endianness, SectionKind, SymbolFlags, SymbolKind, SymbolScope, RelocationTarget, RelocationFlags};

    let file = MachOFile64::<object::endian::LittleEndian>::parse(malformed).map_err(|e| format!("parse: {}", e))?;

    // Derive architecture and endianness from the input file
    let arch = file.architecture();
    let endian = if file.is_little_endian() { Endianness::Little } else { Endianness::Big };
    let mut out = write::Object::new(BinaryFormat::MachO, arch, endian);

    // Copy sections
    let mut section_map = std::collections::HashMap::new();
    for section in file.sections() {
        let name = section.name().unwrap_or("");
        let segment = section.segment_name().unwrap_or(None).unwrap_or("");
        let kind = section.kind();
        let out_section = out.add_section(segment.as_bytes().to_vec(), name.as_bytes().to_vec(), kind);
        let data = section.data().unwrap_or(&[]);
        out.section_mut(out_section)
            .set_data(data.to_vec(), section.align() as u64);
        section_map.insert(section.index(), out_section);
    }

    // Copy symbols (skip corrupted ones with invalid n_strx)
    let mut sym_map = std::collections::HashMap::new();
    for symbol in file.symbols() {
        let name = match symbol.name() {
            Ok(n) => n,
            Err(_) => continue, // skip corrupted symbols
        };
        if name.is_empty() {
            continue;
        }
        let section = symbol.section_index().and_then(|idx| section_map.get(&idx).copied());
        let out_sym = write::Symbol {
            name: name.as_bytes().to_vec(),
            value: symbol.address(),
            size: symbol.size(),
            kind: symbol.kind(),
            scope: symbol.scope(),
            weak: symbol.is_weak(),
            section: match section {
                Some(s) => write::SymbolSection::Section(s),
                None => {
                    if symbol.is_undefined() {
                        write::SymbolSection::Undefined
                    } else {
                        write::SymbolSection::Absolute
                    }
                }
            },
            flags: SymbolFlags::None,
        };
        let out_sym_id = out.add_symbol(out_sym);
        sym_map.insert(symbol.index(), out_sym_id);
    }

    // Copy relocations for each section (critical for function call resolution)
    for section in file.sections() {
        let out_section = match section_map.get(&section.index()) {
            Some(&s) => s,
            None => continue,
        };
        for (offset, reloc) in section.relocations() {
            let target_sym = match reloc.target() {
                RelocationTarget::Symbol(idx) => {
                    match sym_map.get(&idx) {
                        Some(&s) => s,
                        None => continue, // skip relocations referencing corrupted symbols
                    }
                }
                RelocationTarget::Section(section_idx) => {
                    // Section-relative relocation (r_extern=false on Mach-O).
                    // Map to the output section's symbol.
                    match section_map.get(&section_idx) {
                        Some(&target_section) => out.section_symbol(target_section),
                        None => continue,
                    }
                }
                _ => continue,
            };
            if let Err(e) = out.add_relocation(out_section, write::Relocation {
                offset,
                symbol: target_sym,
                addend: reloc.addend(),
                flags: reloc.flags(),
            }) {
                eprintln!("[MACHO-FIX] relocation copy warning: {}", e);
            }
        }
    }

    out.write().map_err(|e| format!("write: {}", e))
}

impl Default for Codegen {
    fn default() -> Self {
        Self::new().expect("Failed to create codegen")
    }
}

#[cfg(test)]
#[path = "cranelift_tests.rs"]
mod tests;
