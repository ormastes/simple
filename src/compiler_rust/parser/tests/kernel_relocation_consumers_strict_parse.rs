use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

const CONSUMERS: [&str; 15] = [
    "src/compiler/35.semantics/layer_call_wiring.spl",
    "src/compiler/35.semantics/interface/compile_interface.spl",
    "src/compiler/35.semantics/interface/module_identity.spl",
    "src/compiler/70.backend/backend/static_backend_registry.spl",
    "src/compiler/80.driver/action_graph/artifact_service_bridge.spl",
    "src/compiler/80.driver/action_graph/demand_compile_integration.spl",
    "src/compiler/80.driver/action_graph/scc_publication_ownership.spl",
    "src/compiler/80.driver/cache/package_index_route.spl",
    "src/compiler/80.driver/cache/package_archive_cache.spl",
    "src/compiler/80.driver/demand_mir_evidence_builder.spl",
    "src/compiler/80.driver/demand_mir_integration.spl",
    "src/compiler/80.driver/driver_api_project_build.spl",
    "src/compiler/80.driver/driver_source_pipeline_loading.spl",
    "src/compiler/80.driver/perf/demand_compile_counters.spl",
    "src/compositions/kernel_llvm_cranelift/compiler/driver/bootstrap_k1_selected.spl",
];

#[test]
fn stage2_failure_consumers_parse_strictly() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    for relative in CONSUMERS {
        let path = repository.join(relative);
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        simple_parser::Parser::new(&source)
            .parse()
            .unwrap_or_else(|error| panic!("{relative} must parse strictly: {error:?}"));
    }

    let owner_manifest = std::env::var("KERNEL_RELOCATION_OWNER_MANIFEST")
        .expect("kernel relocation owner manifest must be provided");
    let owner_paths = fs::read_to_string(&owner_manifest)
        .unwrap_or_else(|error| panic!("failed to read {owner_manifest}: {error}"));
    let canonical_owners: BTreeSet<&str> = owner_paths.lines().filter(|line| !line.is_empty()).collect();
    assert_eq!(canonical_owners.len(), 65);
    assert_eq!(canonical_owners.len(), owner_paths.lines().count());

    for relative in canonical_owners {
        let path = repository.join(relative);
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        simple_parser::Parser::new(&source)
            .parse()
            .unwrap_or_else(|error| panic!("{relative} canonical owner must parse strictly: {error:?}"));
    }
}
