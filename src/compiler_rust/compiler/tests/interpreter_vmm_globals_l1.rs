// L1 lane harness: op-count measurement + regression coverage for the
// `real_vmm_sparse_init_preserves_active_root` ExecutionLimitExceeded red.
//
// Root-cause question: infinite loop from a stale global read vs. genuinely
// heavy test. This harness raises the execution limit, proves termination,
// and attributes op counts per phase (mmio reset / pmm init / vmm sparse
// init / active-root read) so the hotspot is measurable, not guessed.

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 800_000_000;

fn run_program(source: &str) -> (Result<i32, String>, u64) {
    let dir = tempdir().unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, source).unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    simple_compiler::reset_execution_count();
    let result = interpreter::evaluate_module(&module.items);
    let ops = simple_compiler::get_execution_count();
    interpreter::set_current_file(None);
    (result.map_err(|e| format!("{e:?}")), ops)
}

fn vmm_program(body: &str) -> String {
    format!(
        "use os.kernel.boot.mmio.{{mmio_reset_for_test}}\n\
         use os.kernel.memory.pmm.{{pmm_init_identity_range, pmm_get_manager}}\n\
         use os.kernel.memory.vmm.{{vmm_init_sparse_for_test, vmm_active_root}}\n\
         \n\
         fn main() -> i32:\n{body}"
    )
}

/// Phase-attributed op counts. Run with `--nocapture` to see the table.
/// Guards the budget of the real test: the full scenario must fit well
/// under the default 10M-op interpreter limit.
#[test]
fn vmm_sparse_phase_op_counts_fit_default_limit() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);

    let phases: [(&str, String); 4] = [
        (
            "mmio_reset only",
            vmm_program("    mmio_reset_for_test()\n    return 0\n"),
        ),
        (
            "+ pmm_init_identity_range",
            vmm_program(
                "    mmio_reset_for_test()\n    if not pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024):\n        return 1\n    return 0\n",
            ),
        ),
        (
            "+ vmm_init_sparse_for_test",
            vmm_program(
                "    mmio_reset_for_test()\n    if not pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024):\n        return 1\n    if not vmm_init_sparse_for_test(pmm_get_manager(), 0):\n        return 2\n    return 0\n",
            ),
        ),
        (
            "full (+ vmm_active_root)",
            vmm_program(
                "    mmio_reset_for_test()\n    if not pmm_init_identity_range(64 * 1024 * 1024, 1024 * 1024, 2 * 1024 * 1024):\n        return 1\n    if not vmm_init_sparse_for_test(pmm_get_manager(), 0):\n        return 2\n    if vmm_active_root() == 0:\n        return 3\n    return 0\n",
            ),
        ),
    ];

    let mut full_ops = 0u64;
    for (label, source) in &phases {
        let (result, ops) = run_program(source);
        println!("[l1-opcount] {label}: ops={ops} result={result:?}");
        assert_eq!(
            result.as_ref().ok(),
            Some(&0),
            "phase '{label}' failed: {result:?} (ops={ops})"
        );
        full_ops = ops;
    }

    // Restore the default before asserting, so a panic here cannot leak a
    // raised limit into other tests in this binary.
    simple_compiler::set_execution_limit(10_000_000);

    assert!(
        full_ops < 5_000_000,
        "full vmm sparse scenario used {full_ops} ops; budget is <5M to stay clear of the 10M interpreter limit"
    );
}
