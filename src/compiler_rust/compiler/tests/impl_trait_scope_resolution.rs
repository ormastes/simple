//! An impl's trait is resolved through the module system: the trait declared in
//! the impl's own module, else the trait its module imports under that name.
//! Three modules here each declare `trait RenderBackend` with IDENTICAL method
//! names (so the method-overlap fallback cannot tell them apart) and different
//! default bodies; each impl module imports exactly one of them.
//! Runs through the real flatten path (`load_module_with_imports`).

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};

fn trait_module(base: i64) -> String {
    format!("trait RenderBackend:\n    fn id() -> i64\n    me tag() -> i64:\n        {base} + self.id()\n\nexport RenderBackend\n")
}

fn impl_module(trait_mod: &str, class: &str, id: i64) -> String {
    format!(
        "use {trait_mod}.{{RenderBackend}}\n\nclass {class}:\n    var n: i64\n\nimpl RenderBackend for {class}:\n    fn id() -> i64:\n        {id}\n\nexport {class}\n"
    )
}

fn run_dir(files: &[(&str, String)], main: &str) -> i64 {
    let dir = tempfile::tempdir().expect("tempdir");
    for (name, body) in files {
        fs::write(dir.path().join(name), body).unwrap();
    }
    let main_path: PathBuf = dir.path().join("main.spl");
    fs::write(&main_path, main).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .expect("flatten");
    let hir_module = hir::lower(&module).expect("HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("MIR");
    let mut jit = JitCompiler::new_static().expect("JIT");
    jit.compile_module(&mir_module).expect("JIT compile");
    unsafe { jit.call_i64_void("main").expect("run") }
}

fn three_traits() -> Vec<(&'static str, String)> {
    vec![
        ("tra.spl", trait_module(100)),
        ("trb.spl", trait_module(200)),
        ("trc.spl", trait_module(300)),
        ("ia.spl", impl_module("tra", "Ia", 1)),
        ("ib.spl", impl_module("trb", "Ib", 2)),
        ("ic.spl", impl_module("trc", "Ic", 3)),
    ]
}

const MAIN_ALL: &str = "use ia.{Ia}\nuse ib.{Ib}\nuse ic.{Ic}\n\nfn main() -> i64:\n    var a = Ia(n: 0)\n    var b = Ib(n: 0)\n    var c = Ic(n: 0)\n    a.tag() * 1000000 + b.tag() * 1000 + c.tag()\n";

#[test]
fn each_impl_gets_the_trait_its_module_imports() {
    assert_eq!(run_dir(&three_traits(), MAIN_ALL), 101 * 1_000_000 + 202 * 1000 + 303);
}

#[test]
fn import_order_in_main_does_not_change_resolution() {
    let main = "use ic.{Ic}\nuse ia.{Ia}\nuse ib.{Ib}\n\nfn main() -> i64:\n    var a = Ia(n: 0)\n    var b = Ib(n: 0)\n    var c = Ic(n: 0)\n    a.tag() * 1000000 + b.tag() * 1000 + c.tag()\n";
    assert_eq!(run_dir(&three_traits(), main), 101 * 1_000_000 + 202 * 1000 + 303);
}

/// An engine2d backend implementing the four methods the gc trait's default
/// bodies call. Its overlap with BOTH engine2d traits is equal, so only
/// module-scoped resolution can tell which trait it implements.
fn engine_impl(trait_mod: &str, class: &str) -> String {
    format!(
        "use {trait_mod}.{{RenderBackend, Engine2DReadback, engine2d_readback}}\n\nclass {class}:\n    var n: i64\n\nimpl RenderBackend for {class}:\n    fn read_pixels() -> [u32]:\n        []\n    fn read_pixels_with_source() -> Engine2DReadback:\n        engine2d_readback([], \"test\")\n    fn width() -> i32:\n        0\n    fn height() -> i32:\n        0\n\nexport {class}\n"
    )
}

/// The three real stdlib `RenderBackend` traits, verbatim. Only the gc
/// engine2d one declares defaults (`read_pixels_damaged`,
/// `invalidate_damage_mirror`, `read_pixels_region`). Each impl here
/// overrides no trait method, so the overlap fallback alone would give gc's
/// defaults to all three impls (superset tiebreak); module-scoped resolution
/// gives them only to the impl that imports the gc trait.
#[test]
fn each_real_stdlib_render_backend_trait_resolves_by_import() {
    let ui_trait = include_str!("../../../lib/common/ui/backend.spl")
        .replace("use common.ui.widget.{UITree, UIState, UIEvent}", "use widget_stub.{UITree, UIState, UIEvent}");
    let files: Vec<(&str, String)> = vec![
        (
            "widget_stub.spl",
            "class UITree:\n    var n: i64\n\nclass UIState:\n    var n: i64\n\nclass UIEvent:\n    var n: i64\n\nexport UITree, UIState, UIEvent\n"
                .to_string(),
        ),
        ("ui_backend.spl", ui_trait),
        ("nogc_backend.spl", include_str!("../../../lib/nogc_async_mut/gpu/engine2d/backend.spl").to_string()),
        ("gc_backend.spl", include_str!("../../../lib/gc_async_mut/gpu/engine2d/backend.spl").to_string()),
        ("use_ui.spl", "use ui_backend.{RenderBackend}\n\nclass UiImpl:\n    var n: i64\n\nimpl RenderBackend for UiImpl:\n    fn scope_probe() -> i64:\n        1\n\nexport UiImpl\n".to_string()),
        ("use_nogc.spl", engine_impl("nogc_backend", "NogcImpl")),
        ("use_gc.spl", engine_impl("gc_backend", "GcImpl")),
    ];
    let dir = tempfile::tempdir().expect("tempdir");
    for (name, body) in &files {
        fs::write(dir.path().join(name), body).unwrap();
    }
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "use use_ui.{UiImpl}\nuse use_nogc.{NogcImpl}\nuse use_gc.{GcImpl}\n\nfn main() -> i64:\n    0\n",
    )
    .unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .expect("flatten");
    let hir_module = hir::lower(&module).expect("HIR");
    let defaults = ["read_pixels_damaged", "invalidate_damage_mirror", "read_pixels_region"];
    let impl_of = |ty: &str| {
        hir_module
            .impls
            .iter()
            .find(|i| i.type_name == ty && i.trait_name.as_deref() == Some("RenderBackend"))
            .unwrap_or_else(|| panic!("impl RenderBackend for {ty}"))
    };
    for name in defaults {
        assert!(impl_of("GcImpl").methods.contains_key(name), "GcImpl must inherit {name}");
        assert!(!impl_of("NogcImpl").methods.contains_key(name), "NogcImpl must not inherit {name}");
        assert!(!impl_of("UiImpl").methods.contains_key(name), "UiImpl must not inherit {name}");
    }
}

#[test]
fn trait_declared_in_the_impls_own_module_wins() {
    let mut files = three_traits();
    files.push((
        "own.spl",
        "trait RenderBackend:\n    fn id() -> i64\n    me tag() -> i64:\n        900 + self.id()\n\nclass Own:\n    var n: i64\n\nimpl RenderBackend for Own:\n    fn id() -> i64:\n        9\n\nexport Own\n"
            .to_string(),
    ));
    let main = "use ia.{Ia}\nuse own.{Own}\n\nfn main() -> i64:\n    var a = Ia(n: 0)\n    var o = Own(n: 0)\n    a.tag() * 1000 + o.tag()\n";
    assert_eq!(run_dir(&files, main), 101 * 1000 + 909);
}
