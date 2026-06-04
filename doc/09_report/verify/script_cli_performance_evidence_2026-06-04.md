# Script CLI Performance Evidence - 2026-06-04

## Scope

Active `$sp_dev` goal: make Simple script execution competitive with Bun,
Python, and Java without breaking existing script behavior.

## Current Optimization State

The current driver source already contains the script fast path in
`src/compiler_rust/driver/src/exec_core.rs`:

- `.shs` sources prefer interpreter execution.
- CLI-argument scripts detected by `get_cli_args` or `std.cli` prefer
  interpreter execution unless `SIMPLE_EXECUTION_MODE` is explicitly set.
- Interpreted file execution avoids the earlier duplicate parse before
  `load_module_with_imports`.

The normal `bin/simple` symlink target was stale. Rebuilt the optimized driver
with:

```bash
cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml --release
install -m 755 src/compiler_rust/target/release/simple bin/release/x86_64-unknown-linux-gnu/simple
```

## Benchmark

Fixture: tiny CLI script using `std.cli.cli_util.get_cli_args`, compared with
small Python, Bun, and Java programs on the same host.

| Runtime | Runs | Avg ms | Min ms | Max ms | Status |
| --- | ---: | ---: | ---: | ---: | --- |
| Simple `bin/simple run` | 16 | 48 | 44 | 54 | PASS |
| Python 3 | 16 | 26 | 21 | 35 | reference |
| Bun | 16 | 22 | 18 | 30 | reference |
| Java | 16 | 61 | 55 | 76 | reference |

Result: Simple is faster than Java for this script workload and within the same
startup class as Python/Bun.

## Verification

PASS:

- `cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml --release`
- `cargo test -p simple-driver --manifest-path src/compiler_rust/Cargo.toml --lib exec_core::tests -- --nocapture`
  - 5 passed, 0 failed.
- Script runtime smoke: `bin/simple run <cli-args fixture> a b` printed `2`.
- `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.

Known current blocker:

- `SIMPLE_LIB=src bin/simple test test/02_integration/app/startup_argparse_mmap_perf_spec.spl --mode=interpreter --clean`
  fails before timing assertions with `semantic: unknown extern function: shell`.
  The same failure reproduces with `src/compiler_rust/target/debug/simple`, so it
  is not caused by the deployed release binary update.
