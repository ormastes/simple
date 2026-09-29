//! Execute imported private spl_* functions and ambiguous local function values
//! through the actual bootstrap native project builder, including an extern ABI.
#![cfg(feature = "llvm")]

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use std::path::PathBuf;

#[test]
fn imported_optional_struct_restores_callable_field_owner_in_hir_and_mir() {
    use simple_compiler::hir::{HirStmt, HirType, Lowerer, TypeId};
    use simple_compiler::mir::{lower_to_mir, MirInst};
    use simple_compiler::module_resolver::ModuleResolver;
    use simple_parser::Parser;

    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source = repo.join("test/fixtures/native/symbol_owner_binding");
    let main = source.join("main.spl");
    let text = std::fs::read_to_string(&main).unwrap();
    let ast = Parser::new(&text)
        .parse()
        .expect("real imported callback fixture grammar");
    let resolver = ModuleResolver::new(repo, source);
    let hir = Lowerer::with_module_resolver(resolver, main)
        .lower_module(&ast)
        .unwrap();
    let owner = hir.types.lookup("CallbackPort").expect("imported struct owner");
    let Some(HirType::Struct { fields, .. }) = hir.types.get(owner) else {
        panic!("struct metadata")
    };
    assert!(
        matches!(hir.types.get(fields[1].1), Some(HirType::Function { params, ret }) if params == &[TypeId::I64, TypeId::I64] && *ret == TypeId::I64)
    );
    for name in ["inferred_callback", "annotated_callback"] {
        let function = hir.functions.iter().find(|f| f.name == name).unwrap();
        let HirStmt::Let {
            ty, value: Some(value), ..
        } = &function.body[0]
        else {
            panic!("callback binding")
        };
        assert_eq!(
            *ty,
            owner,
            "{name}: binding {:?}; value {:?}",
            hir.types.get(*ty),
            value
        );
        assert_eq!(value.ty, owner, "{name}: coalesce must yield the struct owner");
    }
    for name in ["nil_fallback", "optional_fallback"] {
        let function = hir.functions.iter().find(|f| f.name == name).unwrap();
        let HirStmt::Expr(value) = function.body.last().unwrap() else {
            panic!("nullable fallback expression")
        };
        assert!(
            matches!(hir.types.get(value.ty), Some(HirType::Pointer { inner, .. }) if *inner == owner),
            "{name}: nullable fallback must keep its wrapper"
        );
    }
    let mir = lower_to_mir(&hir).expect("real callback fixture MIR");
    for name in ["inferred_callback", "annotated_callback"] {
        let function = mir.functions.iter().find(|f| f.name == name).unwrap();
        let instructions: Vec<_> = function.blocks.iter().flat_map(|b| &b.instructions).collect();
        assert!(instructions.iter().any(|i| matches!(i, MirInst::IndirectCall { param_types, return_type, args, .. } if param_types == &[TypeId::I64, TypeId::I64] && return_type.eq(&TypeId::I64) && args.len() == 2)), "{name}: {instructions:?}");
        assert!(
            !instructions
                .iter()
                .any(|i| matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name.ends_with(".invoke_fn"))),
            "{name}: callable field must not become a method symbol"
        );
    }
}

struct BootstrapEnvironment(Vec<(&'static str, Option<std::ffi::OsString>)>);

impl BootstrapEnvironment {
    fn enter() -> Self {
        Self(
            ["SIMPLE_BOOTSTRAP", "SIMPLE_NO_STUB_FALLBACK"]
                .into_iter()
                .map(|name| {
                    let previous = std::env::var_os(name);
                    std::env::set_var(name, "1");
                    (name, previous)
                })
                .collect(),
        )
    }
}

impl Drop for BootstrapEnvironment {
    fn drop(&mut self) {
        for (name, previous) in &self.0 {
            match previous {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }
}

#[test]
fn imported_private_functions_struct_slot_values_and_extern_abi_execute() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source = repo.join("test/fixtures/native/symbol_owner_binding");
    let temporary = tempfile::tempdir().unwrap();
    let executable = temporary.path().join(if cfg!(windows) { "probe.exe" } else { "probe" });
    let _environment = BootstrapEnvironment::enter();
    let build = NativeProjectBuilder::new(repo, executable.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join("main.spl"))
        .build();
    let built = match build {
        Ok(built) => built,
        Err(error) => {
            let evidence = temporary.keep();
            panic!(
                "native source-owner function bindings must link successfully: {error}; evidence={}",
                evidence.display()
            );
        }
    };
    let evidence = temporary.keep();
    assert_eq!(built.failed, 0);
    let run = std::process::Command::new(executable).output().unwrap();
    assert!(
        run.status.success(),
        "status={} stdout={} stderr={} evidence={}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr),
        evidence.display()
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "symbol-owner-binding PASS");
}
