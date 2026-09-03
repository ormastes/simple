use simple_compiler::hir;
use simple_parser::Parser;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn assert_environment_reads_classified(repository: &PathBuf, relative: &str, schema: &str) {
    let root = repository.join(relative);
    let mut pending = vec![root];
    while let Some(path) = pending.pop() {
        if path.is_dir() {
            for entry in fs::read_dir(&path).expect("read source directory") {
                pending.push(entry.expect("read source entry").path());
            }
            continue;
        }
        if path.extension().and_then(|value| value.to_str()) != Some("spl") {
            continue;
        }
        let source = fs::read_to_string(&path).expect("read environment consumer");
        for prefix in ["env_get(\"", "rt_env_get(\"", "env_get_nullable(\""] {
            let mut remainder = source.as_str();
            while let Some(start) = remainder.find(prefix) {
                remainder = &remainder[start + prefix.len()..];
                let end = remainder.find('\"').expect("terminated environment name");
                let name = &remainder[..end];
                assert!(schema.contains(&format!("\"{name}\"")),
                    "unclassified native-build environment read {name} in {}",
                    path.display());
                remainder = &remainder[end + 1..];
            }
        }
    }
}

fn owned_environment_read_registry(repository: &PathBuf) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut pending = vec![
        repository.join("src/compiler"),
        repository.join("src/lib"),
        repository.join("src/runtime"),
        repository.join("src/app/cli"),
        repository.join("src/app/io/_CliCompile"),
    ];
    while let Some(path) = pending.pop() {
        if path.is_dir() {
            for entry in fs::read_dir(&path).expect("read owned-code directory") {
                let child = entry.expect("read owned-code entry").path();
                if child.to_string_lossy().contains("/vendor/") {
                    continue;
                }
                pending.push(child);
            }
            continue;
        }
        let extension = path.extension().and_then(|value| value.to_str());
        if extension != Some("spl") && extension != Some("c") {
            continue;
        }
        let source = fs::read_to_string(path).expect("read owned-code source");
        for prefix in ["env_get(\"", "env_get_opt(\"", "env_get_nullable(\"", "getenv(\""] {
            let mut remainder = source.as_str();
            while let Some(start) = remainder.find(prefix) {
                remainder = &remainder[start + prefix.len()..];
                let end = remainder.find('\"').expect("terminated environment read");
                let name = &remainder[..end];
                if !name.is_empty() && name.bytes().all(|byte|
                    byte == b'_' || byte.is_ascii_uppercase() || byte.is_ascii_digit()) {
                    names.insert(name.to_string());
                }
                remainder = &remainder[end + 1..];
            }
        }
    }
    names
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 14_695_981_039_346_656_037_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(1_099_511_628_211);
    }
    hash
}

fn parse_and_lower(repository: &PathBuf, relative: &str) {
    let path = repository.join(relative);
    let source = fs::read_to_string(&path).expect("read source");
    let ast = Parser::new(&source).parse().expect("parse source");
    hir::lower_with_context_and_project_hint(&ast, &path, Some(repository))
        .expect("project-aware lowering");
}

fn parse_only(repository: &PathBuf, relative: &str) {
    let path = repository.join(relative);
    let source = fs::read_to_string(&path).expect("read source");
    Parser::new(&source).parse().expect("parse source");
}

#[test]
fn native_zero_work_admission_precedes_every_compiler_phase() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let orchestration_path = repository.join("src/compiler/80.driver/driver_orchestration.spl");
    let orchestration = fs::read_to_string(orchestration_path).expect("read orchestration");
    let admission = orchestration.find("native_noop_admit_v1(native_noop_request)")
        .expect("preflight admission");
    for phase in [
        "log_phase(\"compile:start\")",
        "self.load_sources_impl()",
        "self.parse_all_committing_impl()",
        "self.lower_to_mir()",
    ] {
        let scheduled = orchestration.find(phase).expect("scheduled phase");
        assert!(admission < scheduled, "admission must precede {phase}");
    }
    assert!(orchestration.contains("compiler_work_counters_zero_v1(work)"));
    assert!(orchestration.contains("SIMPLE_NATIVE_NOOP_FINAL_OUTPUT"));
    assert!(orchestration.contains("native_noop_publish_built_v1"));
    assert!(orchestration.contains("file_copy(native_noop_request_output_v1(native_noop_request), delivery_output)"));
    let native_build = fs::read_to_string(repository.join(
        "src/app/io/_CliCompile/compile_targets.spl")).expect("read native-build wrapper");
    let final_output_export = native_build.find(
        "env_set(\"SIMPLE_NATIVE_NOOP_FINAL_OUTPUT\", output)")
        .expect("canonical final-output transport");
    let driver_start = native_build[final_output_export..].find(
        "compiler_driver_run_compile(driver)").expect("driver invocation");
    let final_output_restore = native_build[final_output_export..].find(
        "env_set(\"SIMPLE_NATIVE_NOOP_FINAL_OUTPUT\", old_native_noop_final_output)")
        .expect("final-output restoration");
    assert!(driver_start < final_output_restore,
        "canonical final output must remain visible throughout compilation");
    let parser_owner = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_source_pipeline_parsing.spl")).expect("read parser owner");
    let hir_owner = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_hir_pipeline_lowering.spl")).expect("read HIR owner");
    let mir_owner = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_pipeline_lowering.spl")).expect("read MIR owner");
    assert!(parser_owner.contains("compiler_work_parser_schedule_v1"));
    assert!(hir_owner.contains("compiler_work_hir_schedule_v1"));
    assert!(mir_owner.contains("compiler_work_mir_schedule_v1"));
    let aot = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_aot_pipeline.spl")).expect("read aot pipeline");
    let native = fs::read_to_string(repository.join(
        "src/compiler/80.driver/driver_aot_native_output.spl")).expect("read native output");
    assert!(native.contains("compiler_work_codegen_schedule_v1"));
    let linker = fs::read_to_string(repository.join(
        "src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl"))
        .expect("read linker owner");
    assert!(linker.contains("compiler_work_link_schedule_v1"));
    let protocol = fs::read_to_string(repository.join(
        "src/compiler/80.driver/cache/native_noop_admission.spl")).expect("read protocol");
    assert!(protocol.contains("content-digest="));
    assert!(protocol.contains("native_noop_ancestry_authenticated_v1"));
    assert!(protocol.contains("ancestry-cycle"));
    assert!(protocol.contains("ancestry-depth-unbounded"));
    assert!(protocol.contains("native_noop_preserve_collision_v1"));
    assert!(protocol.contains("generation-collision-preservation-failed"));
    assert!(protocol.contains("native_noop_frame_v1"));
    assert!(protocol.contains("native_noop_exclusive_stage_v1"));
    assert!(protocol.contains("file_create_excl(candidate, content)"));
    for point in ["generation-write", "generation-rename", "pointer-write", "pointer-rename"] {
        assert!(protocol.contains(point));
    }
    let environment_schema = fs::read_to_string(repository.join(
        "src/compiler/80.driver/cache/native_build_environment_identity.spl"))
        .expect("read canonical environment schema");
    for field in [
        "SIMPLE_NATIVE_BUILD_NO_MANGLE",
        "SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST",
        "SIMPLE_RUNTIME_ACTION_DIGEST",
        "SIMPLE_STDLIB_ACTION_DIGEST",
        "SIMPLE_BOOTSTRAP_STAGE4",
        "SIMPLE_TYPECHECK_PROFILE",
        "SIMPLE_SAFETY_PROFILE",
        "SIMPLE_LINKER",
        "SIMPLE_NATIVE_RUNTIME_BUNDLE",
    ] {
        assert!(environment_schema.contains(&format!("\"{field}\"")),
            "missing canonical environment control {field}");
    }
    assert!(environment_schema.contains("environment-field-unknown"));
    assert!(environment_schema.contains("environment-schema-incomplete"));
    assert_environment_reads_classified(
        &repository, "src/compiler/70.backend", &environment_schema);
    assert_environment_reads_classified(
        &repository, "src/compiler/80.driver", &environment_schema);
    assert_environment_reads_classified(
        &repository, "src/app/io/_CliCompile/compile_targets.spl", &environment_schema);
    let registry = owned_environment_read_registry(&repository);
    assert_eq!(registry.len(), 373,
        "owned-code environment registry changed; classify the new field before updating evidence");
    let registry_text = registry.into_iter().collect::<Vec<_>>().join("\n") + "\n";
    assert_eq!(format!("{:016x}", fnv1a64(registry_text.as_bytes())),
        "d3c4842dba7bbc90",
        "owned-code environment registry digest changed; review compile impact before updating");
    parse_and_lower(&repository, "src/compiler/80.driver/cache/native_noop_admission.spl");
    parse_and_lower(&repository, "src/compiler/80.driver/cache/native_build_environment_identity.spl");
    parse_and_lower(&repository, "src/compiler/80.driver/perf/compiler_work_counters.spl");
    parse_only(&repository, "src/compiler/80.driver/driver_source_pipeline_parsing.spl");
    parse_only(&repository, "src/compiler/80.driver/driver_hir_pipeline_lowering.spl");
    parse_only(&repository, "src/compiler/80.driver/driver_pipeline_lowering.spl");
    parse_only(&repository, "src/compiler/80.driver/driver_orchestration.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/native_zero_work_admission_spec.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/native_zero_work_crash_probe.spl");
}
