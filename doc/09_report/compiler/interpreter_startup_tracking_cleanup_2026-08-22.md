# Interpreter startup tracking-cleanup evidence — 2026-08-22

## Scope and identities

- Host: Linux x86_64.
- Frozen Rust seed: SHA-256 `9c792e6be04c4c74b61770f8d4bffbe5f2b9812724f765d3fe7f13828c9b83fc`.
- Isolated release candidate: SHA-256 `1eb1d360b7f33974e90fe8046c5b88943eb147f0380b8bbcfdd2fa78dfbe88e1`.
- Workload: `test/fixtures/perf/interpreter_hotpath_fib.spl`, oracle `75025`.
- Both syscall rows set `SIMPLE_LOG_FILE=0`, excluding the independent log-rotation directory read.

## Result

`strace -f -c` on the same interpreter workload recorded:

| Metric | Frozen seed | Candidate |
|---|---:|---:|
| `getdents64` calls | 132 | 0 |
| `openat` calls | 85 | 26 |
| `statx` calls | 34 | 24 |
| stdout oracle | 75025 | 75025 |

`strace -f -k` attributed the baseline recursive directory reads to
`simple_driver::cli::init::cleanup_stale_db_files`, walking
`doc/08_tracking/**` and `.simple/**` on every process startup.

Seven startup-only `--version` samples measured with `/usr/bin/time`:

| Metric | Frozen seed | Candidate | Change |
|---|---:|---:|---:|
| mean wall time | 0.0557 s | 0.0257 s | -53.8% |
| median wall time | 0.05 s | 0.02 s | -60.0% |

The candidate RSS was higher, but the candidate also contained another active
parser lane; no RSS improvement is claimed. Full fib wall time is excluded for
the same source-confounding reason. Syscall attribution, output parity, and the
startup-only timing row support only the removal of the startup tree scan.

## Correctness and concurrency

Every deterministic Rust tracking-DB temporary writer found creates or
truncates its own temp before rename. Pure-Simple database atomic writes do the
same. Global suffix cleanup was therefore unnecessary and could unlink another
process's live temp. The compatibility entry point is retained as a deprecated
no-op. Its focused release unit test passed 1/1 and proves an in-progress
`test_db.sdn.tmp` remains byte-identical.

The self-hosted release binary was not available, so these rows are Rust-seed
diagnostics, not Stage-4 bootstrap evidence.
