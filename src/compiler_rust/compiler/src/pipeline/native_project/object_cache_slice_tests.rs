//! Per-module object cache keying: a module's cached object must be reused
//! across changes that cannot affect its bytes, and must be rebuilt across
//! changes that can.
//!
//! Incident (2026-10-19): the per-module key folded a digest of the ENTIRE
//! closure's import map (`GlobalBuildFingerprint.layout`), so a two-file
//! body-only edit in the compiler tree relinked Stage 2 with
//! `compiled=1367 reused=0`, and dropping one `use std.math` import in a
//! Phase 4 full-CLI build gave `0 cached, 2769 to compile`. The r13 -> r14
//! manifests of that lane differ ONLY in `layout=`; producer, target, opt and
//! scope were identical, so this was purely a keying granularity defect.
//!
//! These tests pin both directions on a tiny multi-module archive build:
//! reuse where the module cannot observe the change, rebuild where it can,
//! and -- the oracle -- a reused object is byte-identical to the object a cold
//! build of the same world produces.

use super::{NativeBuildConfig, NativeBuildResult, NativeProjectBuilder};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

const PROV_BASE: &str = "struct Pt:\n    x: i64\n    y: i64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2)\n\nfn provide() -> i64:\n    return 11\n";
const CONS: &str = "use prov.{make_pt, provide, Pt}\n\nfn consume() -> i64:\n    val p: Pt = make_pt()\n    return provide() + p.y\n";
const OTHER: &str = "fn other_value() -> i64:\n    return 5\n";

struct Fixture {
    temp: tempfile::TempDir,
    src: PathBuf,
}

impl Fixture {
    fn new(files: &[(&str, &str)]) -> Self {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(&src).unwrap();
        let fixture = Fixture { temp, src };
        for (name, body) in files {
            fixture.write(name, body);
        }
        fixture
    }

    fn write(&self, name: &str, body: &str) {
        fs::write(self.src.join(format!("{name}.spl")), body).unwrap();
    }

    fn remove(&self, name: &str) {
        fs::remove_file(self.src.join(format!("{name}.spl"))).unwrap();
    }

    fn cache_dir(&self, tag: &str) -> PathBuf {
        self.temp.path().join(format!("cache-{tag}"))
    }

    fn archive(&self, tag: &str) -> PathBuf {
        self.temp.path().join(format!("lib{tag}.a"))
    }

    fn build(&self, tag: &str) -> NativeBuildResult {
        NativeProjectBuilder::new(self.temp.path().to_path_buf(), self.archive(tag))
            .config(NativeBuildConfig {
                emit_archive: true,
                incremental: true,
                parallel: false,
                no_mangle: false,
                backend: "cranelift".to_string(),
                num_threads: Some(1),
                cache_dir: Some(self.cache_dir(tag)),
                ..NativeBuildConfig::default()
            })
            .source_dir(self.src.clone())
            .build()
            .expect("native archive build failed")
    }

    fn objects_dir(&self, tag: &str) -> PathBuf {
        self.cache_dir(tag).join(super::cache_scope_segment()).join("objects")
    }

    fn object_files(&self, tag: &str) -> HashSet<PathBuf> {
        fs::read_dir(self.objects_dir(tag))
            .unwrap()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
            .collect()
    }

    /// Module prefix -> cached object bytes, for every object in the scope dir.
    /// A module that was recompiled has two objects (old and new key); callers
    /// only read modules they expect to be unique.
    fn objects_by_module(&self, tag: &str) -> BTreeMap<String, Vec<Vec<u8>>> {
        let mut out: BTreeMap<String, Vec<Vec<u8>>> = BTreeMap::new();
        for path in self.object_files(tag) {
            let bytes = fs::read(&path).unwrap();
            let module = module_of_object(&bytes).unwrap_or_else(|| panic!("no module symbol in {}", path.display()));
            out.entry(module).or_default().push(bytes);
        }
        out
    }
}

/// Owner module of a cached object: the prefix before the first `__` of any
/// defined global symbol (`cons__consume` -> `cons`).
fn module_of_object(bytes: &[u8]) -> Option<String> {
    use object::{Object, ObjectSymbol};
    let file = object::File::parse(bytes).ok()?;
    file.symbols()
        .filter(|sym| sym.is_definition() && sym.is_global())
        .filter_map(|sym| sym.name().ok().map(str::to_string))
        .filter_map(|name| name.split_once("__").map(|(module, _)| module.to_string()))
        .next()
}

fn recompiled_modules(fixture: &Fixture, tag: &str, before: &HashSet<PathBuf>) -> BTreeSet<String> {
    fixture
        .object_files(tag)
        .difference(before)
        .map(|path| module_of_object(&fs::read(path).unwrap()).unwrap())
        .collect()
}

fn set(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|s| s.to_string()).collect()
}

fn unique_object(objects: &BTreeMap<String, Vec<Vec<u8>>>, module: &str) -> Vec<u8> {
    let entries = objects.get(module).unwrap_or_else(|| panic!("no cached object for module {module}"));
    assert_eq!(entries.len(), 1, "module {module} must have exactly one cached object, got {}", entries.len());
    entries[0].clone()
}

/// Link the archive against the real core-C runtime with a C runner that
/// prints `cons__consume()`, and return the runner's stdout.
#[cfg(target_os = "linux")]
fn run_consume(fixture: &Fixture, tag: &str) -> String {
    use super::tools::{build_core_c_runtime_library, find_c_compiler};
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .unwrap()
        .to_path_buf();
    let runtime = build_core_c_runtime_library(&fixture.temp.path().join("rt")).expect("real core-C runtime");
    let runner = fixture.temp.path().join(format!("runner-{tag}.c"));
    fs::write(
        &runner,
        "#include <stdint.h>\n#include <stdio.h>\nextern int64_t cons__consume(void);\nint main(void) { printf(\"consume=%lld\\n\", (long long)cons__consume()); return 0; }\n",
    )
    .unwrap();
    let executable = fixture.temp.path().join(format!("probe-{tag}"));
    let link = std::process::Command::new(find_c_compiler())
        .arg("-I")
        .arg(repo_root.join("src/runtime"))
        .arg(&runner)
        .arg(fixture.archive(tag))
        .arg(runtime)
        .args(["-Wl,--gc-sections", "-lpthread", "-ldl", "-lm", "-o"])
        .arg(&executable)
        .output()
        .unwrap();
    assert!(link.status.success(), "{}", String::from_utf8_lossy(&link.stderr));
    let output = std::process::Command::new(&executable).output().unwrap();
    assert!(output.status.success(), "runner failed: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

// ---------------------------------------------------------------------------
// Key-derivation units: tokenizer, key naming, span stripping, slice digest.
// ---------------------------------------------------------------------------

#[test]
fn source_tokens_are_identifier_runs_without_numeric_leaders() {
    let tokens = super::source_identifier_tokens("use prov.{make_pt, Pt}\nval p: Pt = make_pt()\nreturn p.y + 12 + 0x1f\n");
    for expected in ["use", "prov", "make_pt", "Pt", "val", "p", "y", "return"] {
        assert!(tokens.contains(expected), "missing token {expected}");
    }
    assert!(!tokens.contains("12") && !tokens.contains("0x1f"), "numeric literals are not identifiers");
}

#[test]
fn key_name_parts_drop_module_prefix_and_split_methods() {
    let parts = |key: &str| super::key_name_parts(key).into_iter().collect::<HashSet<String>>();
    let has = |key: &str, names: &[&str]| {
        let got = parts(key);
        for name in names {
            assert!(got.contains(*name), "{key}: missing {name} in {got:?}");
        }
        got
    };
    // Path words never become standalone parts: they only occur glued to
    // the rest of the key, which no source spells.
    let helper = has("app__mcp__main__helper", &["helper"]);
    for path_word in ["app", "mcp", "main"] {
        assert!(!helper.contains(path_word), "path word {path_word} leaked: {helper:?}");
    }
    has("lib__model__Point_dot_origin", &["Point", "origin"]);
    has("Point.origin", &["Point", "origin"]);
    has("provide", &["provide"]);
    has("rt_alloc", &["rt_alloc"]);
    // Names that themselves contain `__` or non-identifier characters: a
    // "tail after the last `__`" rule indexed these under nothing.
    has("prov__Foo_dot___init__", &["Foo", "__init__"]);
    has("prov____test__", &["__test__"]);
    has("prov__Stack_dot_empty?", &["Stack", "empty"]);
}

#[test]
fn span_free_debug_strips_every_span_group() {
    let arg = simple_parser::ast::Argument {
        name: None,
        value: simple_parser::ast::Expr::Integer(1),
        span: simple_parser::Span::new(10, 20, 3, 4),
        label: None,
    };
    let shifted = simple_parser::ast::Argument {
        name: None,
        value: simple_parser::ast::Expr::Integer(1),
        span: simple_parser::Span::new(99, 120, 7, 1),
        label: None,
    };
    assert_ne!(format!("{arg:?}"), format!("{shifted:?}"), "fixture: raw Debug must carry the span");
    let stripped = super::span_free_debug(&arg);
    assert_eq!(stripped, super::span_free_debug(&shifted));
    assert!(!stripped.contains("Span {"), "{stripped}");
    assert!(stripped.contains("Integer(1)"), "{stripped}");
}

fn import_map_of(files: &[(&str, &str)]) -> super::imports::ImportMapResult {
    let root = PathBuf::from("/tmp/object-cache-slice-unit/src");
    let sources: Vec<(PathBuf, String)> = files
        .iter()
        .map(|(name, body)| (root.join(format!("{name}.spl")), body.to_string()))
        .collect();
    super::imports::build_import_map(&sources, std::slice::from_ref(&root), &root)
}

#[test]
fn slice_digest_ignores_rows_the_module_never_names() {
    let base = import_map_of(&[("prov", PROV_BASE), ("cons", CONS), ("other", OTHER)]);
    let widened = import_map_of(&[
        ("prov", PROV_BASE),
        ("cons", CONS),
        ("other", "fn other_value() -> i64:\n    return 6\n\nstruct Unrelated:\n    a: i64\n    b: i64\n"),
        ("newmod", "fn fresh_fn(k: i64) -> i64:\n    return k\n"),
    ]);
    let before = super::InterfaceSliceIndex::build(&base).digest_for_source(CONS);
    let after = super::InterfaceSliceIndex::build(&widened).digest_for_source(CONS);
    assert_eq!(before, after, "rows cons never names must not enter its slice");
    assert_eq!(before, super::InterfaceSliceIndex::build(&base).digest_for_source(CONS), "deterministic");
}

/// Every module's lowering registers the WHOLE project enum table
/// (`register_global_enums`), and codegen declares each enum as an import, so
/// an enum cons never names still reaches its object bytes (measured: an
/// `UND extra__Mode` symbol). The slice must therefore cover every enum.
#[test]
fn slice_digest_covers_every_enum_because_lowering_registers_them_all() {
    let base = import_map_of(&[("prov", PROV_BASE), ("cons", CONS), ("other", OTHER)]);
    let with_enum = import_map_of(&[
        ("prov", PROV_BASE),
        ("cons", CONS),
        ("other", "fn other_value() -> i64:\n    return 5\n\nenum Gear:\n    Low\n    High\n"),
    ]);
    let with_variant = import_map_of(&[
        ("prov", PROV_BASE),
        ("cons", CONS),
        ("other", "fn other_value() -> i64:\n    return 5\n\nenum Gear:\n    Low\n    High\n    Top\n"),
    ]);
    let d = |r: &super::imports::ImportMapResult| super::InterfaceSliceIndex::build(r).digest_for_source(CONS);
    assert_ne!(d(&base), d(&with_enum), "adding an enum anywhere enters every slice");
    assert_ne!(d(&with_enum), d(&with_variant), "an enum's variant list enters every slice");
}

#[test]
fn slice_digest_tracks_named_struct_fields_signatures_and_field_name_collisions() {
    let base = import_map_of(&[("prov", PROV_BASE), ("cons", CONS), ("other", OTHER)]);
    let before = super::InterfaceSliceIndex::build(&base).digest_for_source(CONS);
    let digest_with_prov = |prov: &str| {
        let result = import_map_of(&[("prov", prov), ("cons", CONS), ("other", OTHER)]);
        super::InterfaceSliceIndex::build(&result).digest_for_source(CONS)
    };
    assert_ne!(before, digest_with_prov(&PROV_BASE.replace("    y: i64\n", "    y: i64\n    z: i64\n")), "field add");
    assert_ne!(before, digest_with_prov(&PROV_BASE.replace("    x: i64\n    y: i64\n", "    y: i64\n    x: i64\n")), "field reorder");
    assert_ne!(before, digest_with_prov(&PROV_BASE.replace("    y: i64\n", "    y: f64\n")), "field type");
    assert_ne!(before, digest_with_prov(&PROV_BASE.replace("fn provide() -> i64", "fn provide(k: i64 = 0) -> i64")), "arity");
    assert_ne!(before, digest_with_prov(&PROV_BASE.replace("fn provide() -> i64", "fn provide() -> f64")), "return type");

    // A struct in an UNRELATED module that declares a field named like one cons
    // reads (`y`) changes the receiver-blind field resolution cons may use, so
    // it must enter cons's slice even though cons never names that struct.
    let colliding = import_map_of(&[
        ("prov", PROV_BASE),
        ("cons", CONS),
        ("other", "fn other_value() -> i64:\n    return 5\n\nstruct Shadow:\n    q: text\n    r: text\n    y: text\n"),
    ]);
    assert_ne!(before, super::InterfaceSliceIndex::build(&colliding).digest_for_source(CONS), "field-name collision");
}

#[test]
fn slice_digest_matches_field_names_only_through_member_access() {
    let shadow = "fn other_value() -> i64:\n    return 5\n\nstruct Shadow:\n    q: text\n    p: text\n";
    let base = import_map_of(&[("prov", PROV_BASE), ("cons", CONS), ("other", OTHER)]);
    let with_shadow = import_map_of(&[("prov", PROV_BASE), ("cons", CONS), ("other", shadow)]);
    // CONS binds a local named `p` and reads `p.y`; it never reads `.p`.
    assert!(super::source_identifier_tokens(CONS).contains("p"));
    assert!(!super::source_member_tokens(CONS).contains("p"));
    assert_eq!(
        super::InterfaceSliceIndex::build(&base).digest_for_source(CONS),
        super::InterfaceSliceIndex::build(&with_shadow).digest_for_source(CONS),
        "a local sharing a foreign field's name is not a dependency on that struct"
    );
    let cons_reads_p = "use prov.{make_pt, Pt}\n\nfn consume(o) -> i64:\n    return o.p\n";
    assert_ne!(
        super::InterfaceSliceIndex::build(&base).digest_for_source(cons_reads_p),
        super::InterfaceSliceIndex::build(&with_shadow).digest_for_source(cons_reads_p),
        "a `.p` access is receiver-blind-resolvable against Shadow, so Shadow is a dependency"
    );
}

#[test]
fn slice_digest_follows_struct_field_types_transitively() {
    // cons names Outer only; Inner is reached through Outer's field type.
    let prov = "struct Inner:\n    v: i64\n\nstruct Outer:\n    inner: Inner\n\nfn make_outer() -> Outer:\n    return Outer(Inner(1))\n";
    let cons = "use prov.{make_outer, Outer}\n\nfn consume() -> Outer:\n    return make_outer()\n";
    let before = super::InterfaceSliceIndex::build(&import_map_of(&[("prov", prov), ("cons", cons)])).digest_for_source(cons);
    let inner_changed = prov.replace("struct Inner:\n    v: i64\n", "struct Inner:\n    w: i64\n    v: i64\n");
    let after = super::InterfaceSliceIndex::build(&import_map_of(&[("prov", &inner_changed), ("cons", cons)])).digest_for_source(cons);
    assert_ne!(before, after, "a layout change in a transitively reached struct must enter the slice");
}

#[test]
fn slice_digest_ignores_body_edits_that_only_shift_declaration_spans() {
    // A method with a defaulted parameter whose default is a call expression
    // (carries Argument spans). Inserting lines above it shifts every span.
    let prov = "class Cfg:\n    n: i64\n    fn probe(self, k: i64 = Cfg.seed(1)) -> i64:\n        return k\n    static fn seed(v: i64) -> i64:\n        return v\n";
    let cons = "use prov.{Cfg}\n\nfn consume(c: Cfg) -> i64:\n    return c.probe()\n";
    let before = super::InterfaceSliceIndex::build(&import_map_of(&[("prov", prov), ("cons", cons)])).digest_for_source(cons);
    let shifted = format!("fn padding_above() -> i64:\n    return 0\n\n\n{prov}");
    let after = super::InterfaceSliceIndex::build(&import_map_of(&[("prov", &shifted), ("cons", cons)])).digest_for_source(cons);
    assert_eq!(before, after, "span-only movement is not an interface change");
}

/// Direction 1: a body-only change in `prov` recompiles ONLY `prov`; the
/// relinked archive carries the new behaviour.
#[cfg(target_os = "linux")]
#[test]
fn body_only_change_recompiles_only_that_module_and_relinks_correctly() {
    let _guard = crate::pipeline::execution::runtime_bundle_env_lock_for_tests()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let fixture = Fixture::new(&[("prov", PROV_BASE), ("cons", CONS), ("other", OTHER)]);
    let cold = fixture.build("t1");
    assert_eq!((cold.compiled, cold.cached), (3, 0), "cold build compiles every module");
    assert_eq!(run_consume(&fixture, "t1"), "consume=13");

    let before = fixture.object_files("t1");
    fixture.write("prov", &PROV_BASE.replace("return 11", "return 12"));
    let warm = fixture.build("t1");
    assert_eq!(
        recompiled_modules(&fixture, "t1", &before),
        set(&["prov"]),
        "a body-only change must recompile only the changed module"
    );
    assert_eq!((warm.compiled, warm.cached), (1, 2));
    assert_eq!(run_consume(&fixture, "t1"), "consume=14", "relinked archive must carry the new body");
}

/// Direction 2: an interface change in `prov` recompiles `prov` AND its
/// dependent `cons`, while the unrelated `other` stays cached.
#[cfg(target_os = "linux")]
#[test]
fn interface_change_recompiles_dependents_and_keeps_unrelated_cached() {
    let variants: [(&str, &str); 5] = [
        (
            "field add",
            "struct Pt:\n    x: i64\n    y: i64\n    z: i64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2, 3)\n\nfn provide() -> i64:\n    return 11\n",
        ),
        (
            "field reorder",
            "struct Pt:\n    y: i64\n    x: i64\n\nfn make_pt() -> Pt:\n    return Pt(2, 1)\n\nfn provide() -> i64:\n    return 11\n",
        ),
        (
            "field type change",
            "struct Pt:\n    x: i64\n    y: f64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2.0)\n\nfn provide() -> i64:\n    return 11\n",
        ),
        (
            "function arity change (defaulted param, caller text unchanged)",
            "struct Pt:\n    x: i64\n    y: i64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2)\n\nfn provide(k: i64 = 0) -> i64:\n    return 11 + k\n",
        ),
        (
            "function return type change",
            "struct Pt:\n    x: i64\n    y: i64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2)\n\nfn provide() -> f64:\n    return 11.0\n",
        ),
    ];
    for (label, prov_changed) in variants {
        let fixture = Fixture::new(&[("prov", PROV_BASE), ("cons", CONS), ("other", OTHER)]);
        let cold = fixture.build("t2");
        assert_eq!((cold.compiled, cold.cached), (3, 0), "{label}: cold build");
        let before = fixture.object_files("t2");
        fixture.write("prov", prov_changed);
        let warm = fixture.build("t2");
        assert_eq!(
            recompiled_modules(&fixture, "t2", &before),
            set(&["cons", "prov"]),
            "{label}: the dependent must be rebuilt and the unrelated module reused"
        );
        assert_eq!((warm.compiled, warm.cached), (2, 1), "{label}: counts");
    }
}

/// Direction 3: dropping an import (and the module it pulled into the closure)
/// recompiles only the importing module.
#[cfg(target_os = "linux")]
#[test]
fn changed_import_set_recompiles_only_the_importing_module() {
    let fixture = Fixture::new(&[
        ("prov", PROV_BASE),
        ("cons", CONS),
        ("other", OTHER),
        ("helper", "fn helper_value() -> i64:\n    return 3\n"),
        ("cons2", "use helper.{helper_value}\n\nfn consume2() -> i64:\n    return helper_value()\n"),
    ]);
    let cold = fixture.build("t3");
    assert_eq!((cold.compiled, cold.cached), (5, 0));
    let before = fixture.object_files("t3");
    fixture.write("cons2", "fn consume2() -> i64:\n    return 3\n");
    fixture.remove("helper");
    let warm = fixture.build("t3");
    assert_eq!(
        recompiled_modules(&fixture, "t3", &before),
        set(&["cons2"]),
        "shrinking the import set must not touch modules that never named the dropped symbols"
    );
    assert_eq!((warm.compiled, warm.cached), (1, 3));
}

/// Oracle: every object the cache REUSES is byte-identical to the object a
/// cold build of the same world produces. This is the contract the key must
/// honour, independent of how the key is derived. Also pins the prerequisite
/// that a module's object is deterministic across builds.
#[cfg(target_os = "linux")]
#[test]
fn reused_objects_are_byte_identical_to_a_cold_build_of_the_same_world() {
    // `prov.provide2`'s PARAMETER type changes below while the caller text is
    // unchanged: parameter types are in no cross-module table, and the native
    // ABI is uniform i64, so the caller's object cannot depend on it. The
    // oracle proves that rather than assuming it.
    let prov_w1 = "struct Pt:\n    x: i64\n    y: i64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2)\n\nfn provide() -> i64:\n    return 11\n\nfn provide2(k: i64) -> i64:\n    return 1\n";
    let cons_w = "use prov.{make_pt, provide, provide2, Pt}\n\nfn consume() -> i64:\n    val p: Pt = make_pt()\n    return provide() + p.y + provide2(1)\n";
    let fixture = Fixture::new(&[("prov", prov_w1), ("cons", cons_w), ("other", OTHER)]);

    // World 1 twice, in separate caches: determinism prerequisite.
    fixture.build("w1a");
    fixture.build("w1b");
    let w1a = fixture.objects_by_module("w1a");
    let w1b = fixture.objects_by_module("w1b");
    for module in ["prov", "cons", "other"] {
        assert_eq!(
            unique_object(&w1a, module),
            unique_object(&w1b, module),
            "{module}: object bytes must be deterministic across builds of the same world"
        );
    }

    // World 2: prov body change + param-type-only change, plus a brand-new
    // module with its own struct and functions. Neither cons nor other can
    // observe any of it. (A new ENUM is observable everywhere -- world 3.)
    let prov_w2 = "struct Pt:\n    x: i64\n    y: i64\n\nfn make_pt() -> Pt:\n    return Pt(1, 2)\n\nfn provide() -> i64:\n    return 12\n\nfn provide2(k: f64) -> i64:\n    return 1\n";
    let extra = "struct Extra:\n    p: i64\n    q: text\n\nfn extra_value(e: Extra) -> i64:\n    return e.p\n";
    fixture.write("prov", prov_w2);
    fixture.write("extra", extra);
    let before = fixture.object_files("w1a");
    let warm = fixture.build("w1a");
    assert_eq!(
        recompiled_modules(&fixture, "w1a", &before),
        set(&["extra", "prov"]),
        "only the changed and the new module may be compiled"
    );
    assert_eq!((warm.compiled, warm.cached), (2, 2));

    // Cold build of world 2 in a fresh cache is the oracle for the reused objects.
    fixture.build("w2");
    let reused = fixture.objects_by_module("w1a");
    let fresh = fixture.objects_by_module("w2");
    for module in ["cons", "other"] {
        assert_eq!(
            unique_object(&reused, module),
            unique_object(&fresh, module),
            "{module}: the reused object must equal the object a cold build of this world produces"
        );
    }

    // World 3: an enum appears in the new module. `register_global_enums`
    // puts it into every module's lowering, so every module must rebuild,
    // and the result must still equal a cold build of world 3.
    fixture.write("extra", &format!("{extra}\nenum Mode:\n    Fast\n    Slow\n"));
    let before3 = fixture.object_files("w1a");
    let warm3 = fixture.build("w1a");
    assert_eq!((warm3.compiled, warm3.cached), (4, 0), "an enum add is observed by every module");
    let mut rebuilt3: BTreeMap<String, Vec<Vec<u8>>> = BTreeMap::new();
    for path in fixture.object_files("w1a").difference(&before3) {
        let bytes = fs::read(path).unwrap();
        rebuilt3.entry(module_of_object(&bytes).unwrap()).or_default().push(bytes);
    }
    fixture.build("w3");
    let fresh3 = fixture.objects_by_module("w3");
    for module in ["prov", "cons", "other", "extra"] {
        assert_eq!(
            unique_object(&rebuilt3, module),
            unique_object(&fresh3, module),
            "{module}: world-3 object must equal a cold build of world 3"
        );
    }
}


// ---------------------------------------------------------------------------
// Opus review (Fable unavailable) FIX items: rows reached by FUZZY lookups,
// dependency injection and HIR-inlined defaults must enter the slice.
// ---------------------------------------------------------------------------

fn digest_of(files: &[(&str, &str)], module_source: &str) -> u64 {
    super::InterfaceSliceIndex::build(&import_map_of(files)).digest_for_source(module_source)
}

/// `resolve_by_suffix` cuts an unresolved `foo_bar` at `_` and binds a unique
/// `bar`; adding `bar` anywhere must therefore reach the caller's slice.
#[test]
fn slice_digest_tracks_rows_reached_by_suffix_fallback() {
    let caller = "fn use_it() -> i64:\n    return helper_bar()\n";
    let without = digest_of(&[("caller", caller), ("other", OTHER)], caller);
    let with_bar = digest_of(&[("caller", caller), ("other", OTHER), ("lib", "fn bar() -> i64:\n    return 1\n")], caller);
    assert_ne!(without, with_bar, "a new `bar` can rebind `helper_bar`");
}

/// `resolve_name_variants` maps `point_norm` to `Point.norm` (and back).
#[test]
fn slice_digest_tracks_joined_type_method_spellings() {
    let caller = "fn use_it(p: i64) -> i64:\n    return point_norm(p)\n";
    let base = "struct Point:\n    x: i64\n\nimpl Point:\n    fn norm(self) -> i64:\n        return 1\n";
    let changed = base.replace("fn norm(self) -> i64", "fn norm(self) -> f64");
    assert_ne!(
        digest_of(&[("caller", caller), ("geo", base)], caller),
        digest_of(&[("caller", caller), ("geo", &changed)], caller),
        "`point_norm` reaches `Point.norm`"
    );
}

/// A trait row pulls in every implementer's rows: DI emits `{Impl}.new` for
/// implementers the injecting module never names.
#[test]
fn slice_digest_follows_trait_implementers() {
    let caller = "fn use_it(s: Store) -> i64:\n    return 1\n";
    let base = "trait Store:\n    fn get(self) -> i64\n\nstruct MemStore:\n    v: i64\n\nimpl Store for MemStore:\n    fn get(self) -> i64:\n        return self.v\n\nimpl MemStore:\n    static fn new() -> MemStore:\n        return MemStore(v: 0)\n";
    let changed = base.replace("static fn new() -> MemStore", "static fn new(k: i64 = 0) -> MemStore");
    assert_ne!(
        digest_of(&[("caller", caller), ("store", base)], caller),
        digest_of(&[("caller", caller), ("store", &changed)], caller),
        "an implementer's constructor change reaches modules that name the trait"
    );
}

/// The HIR import loader inlines a free function's default at each call site,
/// so a default-VALUE-only change is an interface change for callers.
#[test]
fn slice_digest_tracks_free_function_default_values() {
    let caller = "use prov.{provide}\n\nfn use_it() -> i64:\n    return provide()\n";
    let base = "fn provide(k: i64 = 0) -> i64:\n    return k\n";
    let changed = base.replace("= 0", "= 1");
    assert_ne!(
        digest_of(&[("caller", caller), ("prov", base)], caller),
        digest_of(&[("caller", caller), ("prov", &changed)], caller),
        "default-only change must enter the caller's slice"
    );
}

/// Named arguments and pattern fields name a field without a `.`.
#[test]
fn label_tokens_count_as_member_tokens() {
    let tokens = super::ModuleTokens::of_source("val q = Pt(x: 1, y: 2)\nval m = f(a::b)\nval p: Pt = q\n");
    assert!(tokens.members.contains("x") && tokens.members.contains("y"));
    assert!(!tokens.members.contains("a"), "`::` is a path, not a label");
    assert!(!tokens.members.contains("p"), "a top-level `val p: T` binds a local, not a field");
}

/// End to end: a default-value-only change rebuilds the caller and the
/// relinked binary carries the NEW default.
#[cfg(target_os = "linux")]
#[test]
fn default_value_change_recompiles_the_caller_and_relinks_correctly() {
    let prov = PROV_BASE.replace("fn provide() -> i64:\n    return 11\n", "fn provide(k: i64 = 11) -> i64:\n    return k\n");
    let fixture = Fixture::new(&[("prov", prov.as_str()), ("cons", CONS), ("other", OTHER)]);
    fixture.build("d1");
    assert_eq!(run_consume(&fixture, "d1"), "consume=13");
    fixture.write("prov", &prov.replace("= 11", "= 12"));
    let before = fixture.object_files("d1");
    fixture.build("d1");
    assert_eq!(recompiled_modules(&fixture, "d1", &before), set(&["cons", "prov"]));
    assert_eq!(run_consume(&fixture, "d1"), "consume=14", "caller must see the new default");
}
