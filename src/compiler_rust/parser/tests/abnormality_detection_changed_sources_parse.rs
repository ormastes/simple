//! T0 syntax gate for the build/test abnormality-detection feature surface.
//! This does not replace source-matched Stage-4 execution evidence.

use simple_parser::Parser;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()
        .expect("repository root")
}

#[test]
fn changed_simple_sources_parse() {
    let paths = [
        "src/app/build/cli_entry.spl",
        "src/app/perf/main.spl",
        "src/compiler/80.driver/driver_aot_smf_output.spl",
        "src/compiler/80.driver/driver_log_helpers.spl",
        "src/compiler/80.driver/driver_pipeline_aop.spl",
        "src/lib/common/perf/execution_metrics.spl",
        "src/lib/common/perf/execution_metrics_sdn.spl",
        "src/lib/nogc_sync_mut/database/test_extended/database.spl",
        "src/lib/nogc_sync_mut/database/test_extended/tracking.spl",
        "src/lib/nogc_sync_mut/io/resource_scope.spl",
        "src/lib/nogc_sync_mut/test_runner/test_db_compat.spl",
        "src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl",
        "src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl",
        "src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl",
        "src/lib/nogc_sync_mut/test_runner/test_runner_helpers.spl",
        "src/lib/nogc_sync_mut/test_runner/test_runner_metrics.spl",
        "test/01_unit/lib/database/database_test_extended_spec.spl",
        "test/01_unit/app/perf/perf_cli_spec.spl",
        "test/01_unit/lib/perf/execution_metrics_spec.spl",
    ];
    let root = repo_root();
    let mut failures = Vec::new();
    for relative in paths {
        let path = root.join(relative);
        let source = std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        if let Err(error) = Parser::new(&source).parse() {
            failures.push(format!("{relative}: {error}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
