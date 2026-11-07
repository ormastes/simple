//! `--entry-closure --target x86_64-unknown-none --backend cranelift` imported
//! class instantiation
//! (doc/08_tracking/bug/baremetal_entry_closure_class_instantiation_fault_2026-07-06.md).
//!
//! The record's candidates were: (1) module initializers never emitted, (2)/(3)
//! a cross-module constructor/method reference whose mangled name has no
//! definition, so the kernel link binds it to a weak NIL stub from
//! `auto_stubs.c`, and (4) per-module lowering seeing no field layout for an
//! imported class.  This builds the record's probe shape (a shared module with
//! a scalar global read by a static constructor, a heap-typed `[u64]` global
//! mutated by a `me` method, and a class instantiated from the entry module)
//! as a freestanding entry-closure archive and checks the emitted objects.

use object::read::archive::ArchiveFile;
use object::{Object, ObjectSymbol};
use simple_common::target::{Target, TargetArch, TargetOS};
use simple_compiler::optimizations::NativeOptimizationLevel;
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use std::collections::{BTreeSet, HashSet};
use std::path::PathBuf;

const PROBE_MODULE: &str = r#"var _probe_next_id: u64 = 41
var _probe_events: [u64] = []

class ProbeCounter:
    count: u64
    step: u64

impl ProbeCounter:
    static fn new() -> ProbeCounter:
        val id = _probe_next_id
        _probe_next_id = _probe_next_id + 1
        ProbeCounter(count: id, step: 1)

    me bump(v: u64) -> u64:
        _probe_events.push(v)
        self.count = self.count + v * self.step
        self.count

fn probe_events_len() -> u64:
    _probe_events.len() as u64
"#;

const ENTRY: &str = r#"use class_probe.{ProbeCounter, probe_events_len}

fn spl_start() -> u64:
    var c = ProbeCounter.new()
    val bumped = c.bump(1)
    if c.count == 42 and bumped == 42 and probe_events_len() == 1:
        return 1
    0
"#;

struct Members {
    defined: HashSet<String>,
    undefined: BTreeSet<String>,
}

fn normalized(name: &str) -> String {
    name.trim_start_matches('_').to_string()
}

fn build_members() -> Members {
    std::env::set_var("SIMPLE_BOOTSTRAP", "1");
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    std::fs::write(source.join("class_probe.spl"), PROBE_MODULE).unwrap();
    std::fs::write(source.join("probe_entry.spl"), ENTRY).unwrap();
    let output = temporary.path().join("probe.a");
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let result = NativeProjectBuilder::new(repo, output.clone())
        .config(NativeBuildConfig {
            backend: "cranelift".to_string(),
            target: Some(Target::new(TargetArch::X86_64, TargetOS::None)),
            opt_level: NativeOptimizationLevel::Aggressive,
            entry_closure: true,
            emit_archive: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join("probe_entry.spl"))
        .build()
        .expect("freestanding entry-closure archive must build");
    assert_eq!(result.failed, 0, "native units must not fail: {:?}", result.failures);

    let data = std::fs::read(&output).expect("read archive");
    let archive = ArchiveFile::parse(&*data).expect("parse archive");
    let mut defined = HashSet::new();
    let mut undefined = BTreeSet::new();
    for member in archive.members().flatten() {
        let bytes = member.data(&*data).unwrap();
        let Ok(file) = object::File::parse(bytes) else { continue };
        for symbol in file.symbols() {
            let Ok(name) = symbol.name() else { continue };
            if name.is_empty() {
                continue;
            }
            if symbol.is_undefined() {
                undefined.insert(normalized(name));
            } else if symbol.is_definition() {
                defined.insert(normalized(name));
            }
        }
    }
    Members { defined, undefined }
}

#[test]
fn imported_class_references_bind_to_real_definitions_and_module_init_is_emitted() {
    let members = build_members();
    // Every reference that is not a runtime ABI symbol must be satisfied by
    // the closure itself; otherwise the kernel link resolves it to a weak NIL
    // stub (auto_stubs.c) and the first method call on the result faults.
    let unbound: Vec<&String> = members
        .undefined
        .iter()
        .filter(|name| !name.starts_with("rt_") && !members.defined.contains(*name))
        .collect();
    assert!(
        unbound.is_empty(),
        "cross-module references with no definition in the closure: {unbound:?}"
    );
    for (what, needle) in [
        ("constructor", "ProbeCounter_dot_new"),
        ("method", "ProbeCounter_dot_bump"),
    ] {
        assert!(
            members.defined.iter().any(|name| name.ends_with(needle)),
            "{what} {needle} must be defined: {:?}",
            members.defined
        );
    }
    assert!(
        members.defined.iter().any(|name| name.starts_with("module_init")),
        "the heap-typed module global needs an emitted __module_init_* initializer: {:?}",
        members.defined
    );
}
