//! Prevention for bug
//! enum_discriminant_convention_split_hashed_seed_vs_positional_pure_simple_2026-08-08:
//! every seed site that builds or tests an enum discriminant must route through
//! the single runtime definition `simple_runtime::value::hash_variant_discriminant`
//! (positional for Option/Result, matching pure-Simple and the C runtime).
//! A private inline `DefaultHasher ... & 0xFFFFFFFF` copy is how the seed
//! drifted onto a second convention in the first place.

use std::path::Path;

fn scan(dir: &Path, offenders: &mut Vec<String>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            scan(&path, offenders);
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("rs") || path.ends_with(file!().rsplit(['/', '\\']).next().unwrap()) {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        for (i, line) in lines.iter().enumerate() {
            if !line.contains("DefaultHasher::new()") {
                continue;
            }
            let window = lines[i..(i + 4).min(lines.len())].join("\n");
            if window.contains("& 0xFFFFFFFF") || window.contains("& 0xFFFF_FFFF") {
                offenders.push(format!("{}:{}", path.display(), i + 1));
            }
        }
    }
}

#[test]
fn no_inline_hashed_variant_discriminants_in_compiler() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut offenders = Vec::new();
    for sub in ["codegen", "hir", "mir", "interpreter_extern"] {
        scan(&root.join(sub), &mut offenders);
    }
    // The runtime crate owns the single definition (objects.rs); every other
    // runtime file must call it.
    let mut runtime_offenders = Vec::new();
    scan(&root.join("../../runtime/src"), &mut runtime_offenders);
    offenders.extend(runtime_offenders.into_iter().filter(|o| !o.replace('\\', "/").contains("value/objects.rs:")));
    assert!(
        offenders.is_empty(),
        "inline 32-bit DefaultHasher discriminant copies (use hash_variant_discriminant): {offenders:#?}"
    );
}

#[test]
fn seed_builtin_discriminants_match_pure_simple_positional_order() {
    use simple_runtime::value::hash_variant_discriminant as d;
    // Pure-Simple registers Result as `Ok=0, Err=1` and Option as `Some=0,
    // None=1` (50.mir switch_operators_calls.spl, lower_try_expr err_key=1).
    assert_eq!([d("Ok"), d("Err")], [0, 1]);
    assert_eq!([d("Some"), d("None")], [0, 1]);
}

#[test]
fn hir_enum_registration_assigns_declaration_index() {
    use crate::hir::{HirType, TypeRegistry};
    use simple_runtime::value::hash_variant_discriminant as d;
    let mut registry = TypeRegistry::new();
    registry.register_named(
        "UeHirLight".to_string(),
        HirType::Enum {
            name: "UeHirLight".to_string(),
            variants: vec![("UeHirOff".into(), None), ("UeHirDim".into(), None), ("UeHirOn".into(), None)],
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: Default::default(),
        },
    );
    assert_eq!([d("UeHirOff"), d("UeHirDim"), d("UeHirOn")], [0, 1, 2]);
}

/// Every place the seed learns an enum declaration must feed the positional
/// registry; a new `enums.insert(` without it reintroduces name hashing for
/// that path (the interpreter matched by name, native by hashed tag).
#[test]
fn every_interpreter_enum_registration_feeds_positional_registry() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut offenders = Vec::new();
    for file in ["interpreter_eval.rs", "interpreter_sffi.rs"] {
        let text = std::fs::read_to_string(root.join(file)).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        for (i, line) in lines.iter().enumerate() {
            let t = line.trim_start();
            if t.starts_with("enums.insert(e.name.clone(), Arc::new(") || t.starts_with("enums.insert(prefixed_name") {
                let window = lines[i.saturating_sub(3)..i].join("\n");
                if !window.contains("register_enum_variants") {
                    offenders.push(format!("{file}:{}", i + 1));
                }
            }
        }
    }
    let reg = std::fs::read_to_string(root.join("hir/type_registry.rs")).unwrap();
    assert!(reg.matches("note_enum_positions(&ty)").count() >= 2, "TypeRegistry register/update_named must feed positions");
    assert!(offenders.is_empty(), "enum registrations without positional discriminants: {offenders:#?}");
}
