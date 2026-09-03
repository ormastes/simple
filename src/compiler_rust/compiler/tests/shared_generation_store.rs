use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

fn parse_and_lower(repository: &PathBuf, relative: &str) {
    let path = repository.join(relative);
    let source = fs::read_to_string(&path).expect("read source");
    let ast = Parser::new(&source).parse().expect("parse source");
    hir::lower_with_context_and_project_hint(&ast, &path, Some(repository))
        .expect("project-aware lowering");
}
#[test]
fn shared_generation_store_has_durable_publication_and_pinned_gc_contracts() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = repository.join("src/compiler/80.driver/cache/shared_generation_store.spl");
    let source = fs::read_to_string(path).expect("read shared generation store");
    let generation_fsync = source.find("rt_file_fsync(staged)").expect("generation fsync");
    let generation_rename = source.find("rt_file_rename(staged, generation_path)")
        .expect("generation rename");
    let pointer_fsync = source.find("rt_file_fsync(pointer_stage)").expect("pointer fsync");
    let pointer_rename = source.find("rt_file_rename(pointer_stage, \"{root}/CURRENT\")")
        .expect("pointer rename");
    let directory_fsync = source.find("not rt_file_fsync(root)").expect("directory fsync");
    assert!(generation_fsync < generation_rename);
    assert!(generation_rename < pointer_fsync);
    assert!(pointer_fsync < pointer_rename);
    assert!(pointer_rename < directory_fsync);
    assert!(source.contains("shared_generation_is_pinned_v1(candidate, pins)"));
    assert!(source.contains("generation-count-unbounded"));
    assert!(source.contains("lease-count-unbounded"));
    assert!(source.contains("protected-generations-exceed-bound"));
    assert!(source.contains("shared_generation_reclaim_dead_leases_v1"));
    assert!(source.contains("shared_generation_exclusive_stage_v1"));
    assert!(source.contains("file_create_excl(path, content)"));
    assert!(source.contains("rows = rows.sorted()"));
    assert!(source.contains("rt_process_start_identity(owner_pid!)"));
    assert!(source.contains("shared_generation_reclaim_orphan_stages_v1"));
    assert!(source.contains("shared_generation_store_bytes_v1"));
    parse_and_lower(&repository, "src/compiler/80.driver/cache/shared_generation_store.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/shared_generation_publication_spec.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/shared_generation_writer_race_native.spl");
    parse_and_lower(&repository, "test/03_system/compiler/feature/shared_generation_process_death_native.spl");
}
