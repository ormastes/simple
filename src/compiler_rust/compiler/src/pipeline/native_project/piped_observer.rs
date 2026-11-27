//! Explicit core-C observer selection. Never consult environment provider flags.
use object::{Object, ObjectSymbol};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const OBSERVERS: [&str; 2] = [
    "rt_process_stdout_state",
    "rt_process_piped_exit_status_value",
];
const C_CONTRACT: [&str; 6] = [
    "simple_piped_owner_observe_v1",
    "simple_piped_receipt_new_v1",
    "rt_array_new",
    "rt_array_push",
    "rt_array_free",
    "rt_value_int",
];

#[derive(Clone, Debug, Default)]
pub(super) enum PipedObserverSelection {
    #[default]
    CoreC,
    RustObserverOverCoreC(VerifiedObserverArchive),
}

/// Fields stay private: only exact receipt/source/archive verification creates it.
#[derive(Clone, Debug)]
pub(super) struct VerifiedObserverArchive {
    archive: PathBuf,
    target: String,
    hashes: BTreeMap<String, String>,
}

impl PipedObserverSelection {
    pub(super) fn is_rust(&self) -> bool {
        matches!(self, Self::RustObserverOverCoreC(_))
    }

    pub(super) fn c_define(&self) -> Option<&'static str> {
        self.is_rust()
            .then_some("-DSIMPLE_RUNTIME_RUST_PIPED_OBSERVER_V1=1")
    }

    pub(super) fn archive(&self) -> Option<&Path> {
        match self {
            Self::CoreC => None,
            Self::RustObserverOverCoreC(record) => Some(&record.archive),
        }
    }

    pub(super) fn fingerprint(&self) -> String {
        match self {
            Self::CoreC => String::new(), // retain baseline core-C cache identity
            Self::RustObserverOverCoreC(record) => format!(
                "piped-rust-observer-v1;target={};abi=core-c-tagged64-observer-v1;{:?}",
                record.target, record.hashes
            ),
        }
    }

    pub(super) fn read_receipt(
        path: &Path,
        target: simple_common::target::Target,
        runtime_root: &Path,
    ) -> Result<Self, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("observer receipt: {e}"))?;
        let parsed = simple_sdn::parse(&text).map_err(|e| format!("observer SDN: {e}"))?;
        let fields = parsed
            .as_dict()
            .ok_or("observer receipt must be an SDN dictionary")?;
        let string = |key: &str| -> Result<String, String> {
            fields
                .get(key)
                .and_then(|v| v.as_str())
                .map(str::to_string)
                .ok_or_else(|| format!("observer receipt missing text `{key}`"))
        };
        if fields.len() != 9
            || string("schema")? != "piped-native-observer-v1"
            || string("abi")? != "core-c-tagged64-observer-v1"
            || fields.get("bridge_version").and_then(|v| v.as_i64()) != Some(1)
            || string("target_triple")? != target.to_string()
        {
            return Err("observer receipt schema/target/ABI/version mismatch".into());
        }
        let mut hashes = BTreeMap::new();
        for key in [
            "bridge_sha256",
            "c_owner_sha256",
            "rust_source_sha256",
            "archive_sha256",
        ] {
            let digest = string(key)?;
            if digest.len() != 64
                || !digest
                    .bytes()
                    .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
            {
                return Err(format!("observer malformed `{key}`"));
            }
            hashes.insert(key.to_string(), digest);
        }
        let archive = PathBuf::from(string("archive_path")?);
        let archive = if archive.is_absolute() {
            archive
        } else {
            path.parent()
                .ok_or("observer receipt has no parent")?
                .join(archive)
        };
        let selected = Self::RustObserverOverCoreC(VerifiedObserverArchive {
            archive,
            target: target.to_string(),
            hashes,
        });
        selected.validate(target, runtime_root)?;
        Ok(selected)
    }

    pub(super) fn validate(
        &self,
        target: simple_common::target::Target,
        runtime_root: &Path,
    ) -> Result<(), String> {
        let Self::RustObserverOverCoreC(record) = self else {
            return Ok(());
        };
        if record.target != target.to_string() {
            return Err("observer target changed after selection".into());
        }
        if !matches!(
            target.arch,
            simple_common::target::TargetArch::X86_64
                | simple_common::target::TargetArch::Aarch64
                | simple_common::target::TargetArch::Riscv64
        ) {
            return Err("observer core-C tagged64 ABI requires a 64-bit target".into());
        }
        let src = runtime_root
            .parent()
            .ok_or("observer runtime source parent missing")?;
        for (key, path) in [
            ("archive_sha256", record.archive.clone()),
            ("c_owner_sha256", runtime_root.join("runtime_process.c")),
            (
                "bridge_sha256",
                runtime_root.join("runtime_process_observer_private.h"),
            ),
            (
                "rust_source_sha256",
                src.join("compiler_rust/runtime/src/piped_process_observer.rs"),
            ),
        ] {
            if super::config::bootstrap_tools_file_sha256(&path)? != record.hashes[key] {
                return Err(format!("observer `{key}` changed: {}", path.display()));
            }
        }
        let symbols = read_symbols_for_target(&record.archive, true, target)?;
        for symbol in OBSERVERS {
            require_strong(&symbols, symbol, 1)?;
        }
        for symbol in symbols.keys() {
            if (symbol.starts_with("rt_")
                || symbol.starts_with("spl_")
                || symbol.starts_with("simple_"))
                && !OBSERVERS.contains(&symbol.as_str())
            {
                return Err(format!(
                    "observer archive brings unrelated runtime provider `{symbol}`"
                ));
            }
        }
        Ok(())
    }

    pub(super) fn verify_link_inputs(
        &self,
        core: &Path,
        objects: &[PathBuf],
    ) -> Result<(), String> {
        let Some(archive) = self.archive() else {
            return Ok(());
        };
        let c_symbols = read_symbols(core, true)?;
        for symbol in OBSERVERS {
            require_strong(&c_symbols, symbol, 0)?;
        }
        for symbol in C_CONTRACT {
            require_strong(&c_symbols, symbol, 1)?;
        }
        // Application/extra objects cannot shadow either selected provider family.
        for path in objects.iter().filter(|p| p.as_path() != archive) {
            let symbols = read_symbols(path, false)?;
            for symbol in OBSERVERS.into_iter().chain(C_CONTRACT) {
                require_strong(&symbols, symbol, 0)?;
            }
        }
        Ok(())
    }

    pub(super) fn link_roots(&self, msvc: bool) -> Vec<String> {
        if !self.is_rust() {
            return Vec::new();
        }
        OBSERVERS
            .into_iter()
            .chain(C_CONTRACT)
            .map(|symbol| {
                if msvc {
                    format!("/include:{symbol}")
                } else if super::effective_target().os == simple_common::target::TargetOS::MacOS {
                    format!("-Wl,-u,_{symbol}")
                } else {
                    format!("-Wl,--undefined={symbol}")
                }
            })
            .collect()
    }

    pub(super) fn verify_image(&self, path: &Path) -> Result<(), String> {
        if !self.is_rust() {
            return Ok(());
        }
        let symbols = read_symbols(path, false)?;
        for symbol in OBSERVERS.into_iter().chain(C_CONTRACT) {
            require_strong(&symbols, symbol, 1)?;
        }
        Ok(())
    }
}

/// Count definitions rather than using nm's name-only set, which loses weak and
/// duplicate providers. Target/format checks are applied to every archive member.
fn read_symbols(path: &Path, archive: bool) -> Result<BTreeMap<String, (usize, usize)>, String> {
    read_symbols_for_target(path, archive, super::effective_target())
}

fn read_symbols_for_target(
    path: &Path,
    archive: bool,
    target: simple_common::target::Target,
) -> Result<BTreeMap<String, (usize, usize)>, String> {
    let bytes =
        std::fs::read(path).map_err(|e| format!("observer symbols {}: {e}", path.display()))?;
    let mut result = BTreeMap::new();
    let mut add = |data: &[u8]| -> Result<(), String> {
        let file = object::File::parse(data)
            .map_err(|e| format!("observer object {}: {e}", path.display()))?;
        let expected = super::object_identity_for_target(target);
        if archive
            && (file.architecture() != expected.0 || file.format() != expected.1 || !file.is_64())
        {
            return Err(format!(
                "observer archive member target/ABI mismatch: {}",
                path.display()
            ));
        }
        for symbol in file
            .symbols()
            .filter(|s| s.is_definition() && s.is_global())
        {
            let raw = symbol.name().map_err(|e| e.to_string())?;
            let name = if file.format() == object::BinaryFormat::MachO {
                raw.strip_prefix('_').unwrap_or(raw)
            } else {
                raw
            };
            let counts = result.entry(name.to_string()).or_insert((0, 0));
            if symbol.is_weak() {
                counts.1 += 1;
            } else {
                counts.0 += 1;
            }
        }
        Ok(())
    };
    if archive || bytes.starts_with(b"!<arch>\n") {
        let ar = object::read::archive::ArchiveFile::parse(bytes.as_slice())
            .map_err(|e| e.to_string())?;
        let mut count = 0;
        for member in ar.members() {
            let member = member.map_err(|e| e.to_string())?;
            add(member.data(bytes.as_slice()).map_err(|e| e.to_string())?)?;
            count += 1;
        }
        if count == 0 {
            return Err("observer archive has no objects".into());
        }
    } else {
        add(&bytes)?;
    }
    Ok(result)
}

fn require_strong(
    symbols: &BTreeMap<String, (usize, usize)>,
    name: &str,
    count: usize,
) -> Result<(), String> {
    let actual = symbols.get(name).copied().unwrap_or((0, 0));
    if actual != (count, 0) {
        return Err(format!(
            "observer provider `{name}` expected ({count},0weak), got {actual:?}"
        ));
    }
    Ok(())
}

impl super::NativeProjectBuilder {
    /// Select a real Rust observer archive through the production runtime owner.
    /// Verification failure leaves this builder's previous selection unchanged.
    pub fn set_piped_observer_receipt(&mut self, path: &Path) -> Result<(), String> {
        let root = super::tools::find_core_c_runtime_source_root()
            .ok_or("observer core-C source root absent")?;
        let target = self.config.target.unwrap_or_else(super::effective_target);
        let selected = PipedObserverSelection::read_receipt(path, target, &root)?;
        self.validate_piped_observer_selection(&selected)?;
        self.piped_observer = selected;
        Ok(())
    }

    pub(super) fn validate_piped_observer_lane(&self) -> Result<(), String> {
        self.validate_piped_observer_selection(&self.piped_observer)
    }

    fn validate_piped_observer_selection(
        &self,
        selected: &PipedObserverSelection,
    ) -> Result<(), String> {
        if !selected.is_rust() {
            return Ok(());
        }
        if self.resolve_runtime_lane() != super::NativeRuntimeLane::CoreCBootstrap
            || self.is_authorized_stage4_compiler_entry()
            || self.config.emit_archive
        {
            return Err(
                "Rust piped observer requires the hosted application core-c-bootstrap lane".into(),
            );
        }
        let target = self.config.target.unwrap_or_else(super::effective_target);
        if !matches!(
            target.os,
            simple_common::target::TargetOS::Windows
                | simple_common::target::TargetOS::Linux
                | simple_common::target::TargetOS::FreeBSD
                | simple_common::target::TargetOS::MacOS
        ) {
            return Err("Rust piped observer requires a supported hosted OS".into());
        }
        let root = super::tools::find_core_c_runtime_source_root()
            .ok_or("observer core-C source root absent")?;
        selected.validate(target, &root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn default_keeps_c_exports_and_cache_identity() {
        let selected = PipedObserverSelection::default();
        assert!(!selected.is_rust());
        assert!(selected.archive().is_none());
        assert!(selected.c_define().is_none());
        assert!(selected.fingerprint().is_empty());
        assert!(selected.link_roots(false).is_empty());
    }
    #[test]
    fn weak_duplicate_and_missing_definitions_fail() {
        let mut symbols = BTreeMap::new();
        assert!(require_strong(&symbols, OBSERVERS[0], 1).is_err());
        symbols.insert(OBSERVERS[0].into(), (0, 1));
        assert!(require_strong(&symbols, OBSERVERS[0], 1).is_err());
        symbols.insert(OBSERVERS[0].into(), (2, 0));
        assert!(require_strong(&symbols, OBSERVERS[0], 1).is_err());
        symbols.insert(OBSERVERS[0].into(), (1, 0));
        assert!(require_strong(&symbols, OBSERVERS[0], 1).is_ok());
    }
    #[test]
    fn malformed_selection_never_suppresses_c() {
        let temp = tempfile::tempdir().unwrap();
        let receipt = temp.path().join("observer.sdn");
        std::fs::write(&receipt, "schema: wrong\n").unwrap();
        assert!(PipedObserverSelection::read_receipt(
            &receipt,
            super::super::effective_target(),
            temp.path()
        )
        .is_err());
        assert!(!PipedObserverSelection::CoreC.is_rust());
    }

    #[test]
    fn complete_receipt_without_real_archive_is_rejected() {
        let temp = tempfile::tempdir().unwrap();
        let receipt = temp.path().join("observer.sdn");
        let target = super::super::effective_target();
        let source = format!(
            "schema: \"piped-native-observer-v1\"\ntarget_triple: \"{target}\"\n\
             abi: \"core-c-tagged64-observer-v1\"\nbridge_version: 1\n\
             bridge_sha256: \"{0}\"\nc_owner_sha256: \"{0}\"\n\
             rust_source_sha256: \"{0}\"\narchive_path: \"missing-real-observer.a\"\n\
             archive_sha256: \"{0}\"\n",
            "a".repeat(64)
        );
        std::fs::write(&receipt, source).unwrap();
        let error =
            PipedObserverSelection::read_receipt(&receipt, target, temp.path()).unwrap_err();
        assert!(error.contains("missing-real-observer.a"), "{error}");
        assert!(PipedObserverSelection::CoreC.c_define().is_none());
    }

    #[test]
    fn failed_public_selection_preserves_default_builder() {
        let temp = tempfile::tempdir().unwrap();
        let mut builder =
            super::super::NativeProjectBuilder::new(temp.path().into(), temp.path().join("out"));
        assert!(builder
            .set_piped_observer_receipt(&temp.path().join("absent.sdn"))
            .is_err());
        assert!(builder.piped_observer.c_define().is_none());
        assert!(builder.piped_observer.archive().is_none());
    }

    #[test]
    fn archive_bridge_owner_source_and_target_all_invalidate_cache_identity() {
        let record = VerifiedObserverArchive {
            archive: PathBuf::from("archive.a"),
            target: "target-one".into(),
            hashes: [
                "archive_sha256",
                "bridge_sha256",
                "c_owner_sha256",
                "rust_source_sha256",
            ]
            .into_iter()
            .map(|key| (key.into(), "a".repeat(64)))
            .collect(),
        };
        let base = PipedObserverSelection::RustObserverOverCoreC(record.clone()).fingerprint();
        assert_ne!(base, PipedObserverSelection::CoreC.fingerprint());
        for key in [
            "archive_sha256",
            "bridge_sha256",
            "c_owner_sha256",
            "rust_source_sha256",
        ] {
            let mut changed = record.clone();
            changed.hashes.insert(key.into(), "b".repeat(64));
            assert_ne!(
                base,
                PipedObserverSelection::RustObserverOverCoreC(changed).fingerprint()
            );
        }
        let mut changed = record;
        changed.target = "target-two".into();
        assert_ne!(
            base,
            PipedObserverSelection::RustObserverOverCoreC(changed).fingerprint()
        );
    }
}
