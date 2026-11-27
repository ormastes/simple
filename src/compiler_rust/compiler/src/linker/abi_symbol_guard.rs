//! Fail the link when a runtime-ABI symbol is defined by more than one input.
//!
//! The seed links with `--allow-multiple-definition` whenever extra stub
//! archives are present, so a second strong `rt_enum_new` (e.g. a C runtime
//! object linked next to the Rust `libsimple_runtime.a`) is silently resolved
//! by link order. The two runtimes historically disagreed on the enum
//! discriminant encoding, so whichever definition won decided how every enum
//! in the binary decoded. See
//! doc/08_tracking/bug/enum_discriminant_convention_split_hashed_seed_vs_positional_pure_simple_2026-08-08.md.

use std::path::{Path, PathBuf};

use object::read::archive::ArchiveFile;
use object::{Object, ObjectSymbol};

use super::{LinkerError, LinkerResult};

/// Symbols that must have exactly one definition across all link inputs.
pub(crate) const ABI_UNIQUE_SYMBOLS: &[&str] = &["rt_enum_new"];

fn strip_prefix(name: &str) -> &str {
    name.strip_prefix('_').unwrap_or(name)
}

fn collect_object(data: &[u8], origin: String, hits: &mut Vec<(String, String)>) {
    let Ok(obj) = object::File::parse(data) else {
        return;
    };
    for sym in obj.symbols() {
        if sym.is_undefined() || !sym.is_global() {
            continue;
        }
        let Ok(name) = sym.name() else { continue };
        let name = strip_prefix(name);
        if ABI_UNIQUE_SYMBOLS.contains(&name) {
            hits.push((name.to_string(), origin.clone()));
        }
    }
}

fn collect_input(path: &Path, hits: &mut Vec<(String, String)>) {
    let Ok(data) = std::fs::read(path) else {
        return;
    };
    if let Ok(archive) = ArchiveFile::parse(&*data) {
        for member in archive.members().flatten() {
            let Ok(bytes) = member.data(&*data) else { continue };
            let origin = format!("{}({})", path.display(), String::from_utf8_lossy(member.name()));
            collect_object(bytes, origin, hits);
        }
    } else {
        collect_object(&data, path.display().to_string(), hits);
    }
}

/// Return an error naming every ABI symbol defined by two or more inputs.
pub(crate) fn check_unique_abi_definitions(inputs: &[PathBuf]) -> LinkerResult<()> {
    let mut hits = Vec::new();
    for input in inputs {
        collect_input(input, &mut hits);
    }
    let mut problems = Vec::new();
    for sym in ABI_UNIQUE_SYMBOLS {
        let origins: Vec<&str> = hits.iter().filter(|(n, _)| n == sym).map(|(_, o)| o.as_str()).collect();
        if origins.len() > 1 {
            problems.push(format!("{sym} defined {} times: {}", origins.len(), origins.join(", ")));
        }
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(LinkerError::LinkerFailed {
            exit_code: 1,
            message: format!("duplicate runtime ABI definition ({})", problems.join("; ")),
            stderr: String::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use object::write::{Object as WObject, Symbol, SymbolSection};
    use object::{Architecture, BinaryFormat, Endianness, SymbolFlags, SymbolKind, SymbolScope};

    fn obj_defining(dir: &Path, file: &str, sym: &str) -> PathBuf {
        let mut o = WObject::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
        let text = o.section_id(object::write::StandardSection::Text);
        let off = o.append_section_data(text, &[0xc3], 1);
        o.add_symbol(Symbol {
            name: sym.as_bytes().to_vec(),
            value: off,
            size: 1,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
        let p = dir.join(file);
        std::fs::write(&p, o.write().unwrap()).unwrap();
        p
    }

    #[test]
    fn duplicate_rt_enum_new_fails_the_link() {
        let d = tempfile::tempdir().unwrap();
        let a = obj_defining(d.path(), "rust_rt.o", "rt_enum_new");
        let b = obj_defining(d.path(), "c_rt.o", "rt_enum_new");
        let err = check_unique_abi_definitions(&[a, b]).unwrap_err().to_string();
        assert!(err.contains("rt_enum_new defined 2 times"), "{err}");
        assert!(err.contains("rust_rt.o") && err.contains("c_rt.o"), "{err}");
    }

    #[test]
    fn single_rt_enum_new_and_unrelated_duplicates_pass() {
        let d = tempfile::tempdir().unwrap();
        let a = obj_defining(d.path(), "rt.o", "rt_enum_new");
        let b = obj_defining(d.path(), "x1.o", "helper");
        let c = obj_defining(d.path(), "x2.o", "helper");
        assert!(check_unique_abi_definitions(&[a, b, c]).is_ok());
    }

    #[test]
    fn mach_o_underscore_prefix_is_still_detected() {
        let d = tempfile::tempdir().unwrap();
        let a = obj_defining(d.path(), "a.o", "_rt_enum_new");
        let b = obj_defining(d.path(), "b.o", "rt_enum_new");
        assert!(check_unique_abi_definitions(&[a, b]).is_err());
    }
}
