# Bug: sspec test runner kills a heavy subprocess example at a fixed 10s timeout
## RESOLVED 2026-11-25 — timeout is now configurable (`SIMPLE_TIMEOUT_SECONDS`, `0` disables); verified live on the pinned v1.0.0-rc.1 binary (see note at bottom)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-06-29
**Severity:** medium (workaround: keep per-example subprocess work under ~10s)
**Found while:** running the NVMe firmware system spec
(`test/03_system/app/nvme_firmware/nvme_firmware_simulation_spec.spl`) after folding the
heavy production-hardening regressions into `test_fw.spl`.

## Symptom
A subprocess sspec example that runs a child process taking longer than **10 seconds**
is killed. The runner surfaces this as:
- the example marked `✗`, but the **file-level tally still reports `Failed: 0` / `PASS`**
  (so it is easy to miss — a red mark that is not counted as a failure);
- `process_run` returns `code == 1` with **partial** captured stdout (whatever the child
  wrote before the kill) and an **empty** captured `err` — the actual cause
  (`error: example timed out after 10s: <file>`) goes to the *runner's* stderr, not the
  example's captured `err`, so it is invisible from inside the spec.

The same child runs green and exit-0 via `bin/simple run <file>` and via plain
`sh -c "bin/simple run <file>"` (no 10s cap there) — the timeout is imposed only on the
example when run under `bin/simple test`.

## Reproduction
`test_fw.spl` (the full HIL/FTL/FIL + controller self-test suite) once it also ran the
heavy regressions (a ~4k-write GC-reserve fill, a 600-write WAL-overflow case, and a
wear-leveling churn, each plus a full L2P/band recovery scan) took ~8–10s nested and
tipped over the 10s cap. Confirmed by redirecting the child's stderr to a file from
inside a diag spec (`sh -c "... 2>/tmp/err.txt"` + `file_read_text`), which dodges the
partial-stdout capture and shows `error: example timed out after 10s`.

## Workaround (applied)
Keep each subprocess example's child under ~10s. The heavy NVMe regressions live as
separate standalone runnable checks (`fw/{gc_safety_check,durability_check,wear_scrub_check}.spl`),
each of which fits under 10s and is a distinct sspec example; `test_fw.spl` keeps only the
fast leaf + integration self-tests. The full aggregate is the `bin/simple run test_fw.spl`
gate per `fw/CONVENTIONS.md`.

## Desired fix
A configurable per-example timeout (or a longer default for `03_system` specs), and on
timeout, surface the timeout reason in the example's captured `err` (or a distinct status)
so a spec can distinguish "child timed out" from "child failed", instead of a silent
partial capture with `code == 1`.


## Verification 2026-11-25 (release/1.0.0 HEAD 4bc2c986375, work/p2w5-aa lane)

The "Desired fix" is landed in the runner's safety policy
(`src/compiler_rust/driver/src/cli/examples_safety.rs`) and verified LIVE on
the pinned tracked binary `bin/simple.exe` (Simple v1.0.0-rc.1):

- The 10s default is now overridable: `examples_timeout_secs()` reads
  `SIMPLE_TIMEOUT_SECONDS` (positive value wins; `0` disables the watchdog
  and child isolation entirely — `examples_safety.rs:22-43`).
- Probe: an examples-path file whose `main` sleeps 12s
  (`rt_sleep_ms(12000)`):
  - default: killed at 10s with `error: example timed out after 10s: <path>`
    (10.4s wall) — the original behavior, reproduced;
  - `SIMPLE_TIMEOUT_SECONDS=30`: child runs to completion, prints its marker,
    rc=0 (12.4s wall).
- The timeout reason now reaches the parent's stderr: the runner tees the
  child's stdout/stderr on dedicated threads and prints the timeout message
  after the kill (`run_child_with_timeout_and_writers`,
  `examples_safety.rs:141-205`), with Rust unit tests covering output
  retention across the kill (`timeout_kills_real_process_and_retains_routed_output`).
  The original "silent partial capture, reason invisible" symptom is thereby
  mitigated at the runner level.

Residual, stated honestly: the timeout reason is still not injected into a
spec's own captured `err` string as a distinct status (that would be a
spec-side `process_run` contract change); a spec that needs to distinguish
"child timed out" from "child failed" should still size its children or set
`SIMPLE_TIMEOUT_SECONDS`. The primary ask — a configurable per-example
timeout — is implemented and verified, and the documented workaround
(per-check files under ~10s) remains valid. Closing as RESOLVED.
