<!-- codex-research -->
# Aspect dynload test/coverage static ledger — 2026-08-26

**Status: UNVERIFIED.** This is a source-and-receipt inventory only.  No test,
build, bootstrap, parity benchmark, coverage tool, or guard was run to prepare
it.  It records neither current PASS nor current FAIL.

## Scope and admissibility

The governing plan is
`doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`,
§§3.1, 3.4, 3.7 and lanes A/D/H.  It explicitly rejects seed-only checks,
stale receipts, tautologies, empty denominators, and unavailable-platform skips
as PASS.  The plan requires a revision-, mode-, compiler-, and host-pinned,
deduplicated manifest before it can make a current suite or coverage claim.

No such checked-in lane-A manifest or retained current lane-D branch-coverage
receipt was found in the focused evidence paths below.  `build/coverage/coverage.sdn`,
which the plan names as a historical zero-denominator report, is absent in this
worktree; absence is not evidence that coverage passed or failed.

## Evidence ledger

| Evidence path | What the record says | Static classification now | Host-fixable classification |
|---|---|---|---|
| `doc/08_tracking/bug/gated_specs_are_tautology_shells_2026-08-09.md` | 27 gated files: 12 tautology shells and 7 reported genuine defects; remaining rows were real-body PASS/dropped cases | Historical source, not a current count; individual files need manifest reconciliation | Test-source assertions/false closed-gate expectations: **candidate host-fixable**. Real GPU/CUDA/Vulkan/LLVM/VHDL outcomes: **environment-dependent until reproduced**. Metal dropped case remains explicit unavailable. |
| `doc/08_tracking/test/expect_vacuity_gate_full_corpus_census.md` | 2026-08-10 Rust-seed census: 2,372/9,872 deduplicated specs executed; 200 infra and 116 no-verdict rows | Historical and incomplete; its seed binary identity must not clear current Simple ownership | Vacuous examples and static parse/module rows: **candidate host-fixable**. Timeout/no-verdict rows include host contention but also unresolved-module, zero-example, parse, OOM, and signal possibilities; retain their raw diagnostic and classify only after one pinned replay on a quiet host. |
| `doc/08_tracking/test/failure_taxonomy_2026-08-18.md` | Sharded taxonomy, with duplicate trees called out | Historical triage only; not additive with mirror results | Classes require current pinned replay; do not mass-fix from this table. |
| `doc/08_tracking/test/failure_taxonomy_system_unit_2026-08-18.md` | Many system/unit directory shards were inconclusive; reported object-erasure results | Superseded as failure evidence by the runner-path defect record below | **Do not repair as a product failure** until a current manifest uses the binary under test. |
| `doc/08_tracking/bug/directory_test_runs_spawn_deployed_bin_simple_not_binary_under_test_2026-08-19.md` | `find_simple_binary()` was fixed to resolve `/proc` executable identity | Historical taxonomy that used directory targets is invalid for current-failure accounting | Source repair is recorded FIXED; Linux/FreeBSD path is host-usable, while macOS/Windows remain an explicit fallback gap. |
| `doc/03_plan/compiler/aspect_dynload/lane_resume_plan_2026-08-18.md` | Five focused loader/SIF specs green, `segment_symbol_resolution_spec` 7/8 with mapped-code execution returning zero | Historical focused receipt only; it is a real positive-control failure, not a reason to weaken the spec | **Candidate host-fixable** loader/source-offset/protection/ICache path, but runtime evidence is required before closure. |
| `doc/08_tracking/bug/interpreter_thread_spawn_runs_inline_all_concurrency_tests_vacuous_2026-08-19.md` | Interpreter spawn inlined closures; Bool CAS was fake; native proof was then backend-blocked | Concurrency assertions executed through that interpreter path are non-evidence | **Candidate host-fixable** runtime semantics; acceptance must use a real native thread path, so interpreter-only replay is insufficient. |
| `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md` and `scripts/check/check-stage-binaries-runnable.shs` | Stale stage artifact cause partly repaired; tracked stage binaries are absent/untracked and guard is expected to be non-green until redeploy | Bootstrap is a missing-artifact/provenance condition, not a suite failure | **Potentially host-fixable** only after a current Stage 2/3 build can be generated; no Stage 4/deploy claim may be inferred. |
| `test/perf/io_parity/{io_parity_simple.spl,io_parity_ref.c,io_parity_ref.rs,run_io_parity_benchmarks.shs}` | C/Rust/Simple harness exists | Not an admissible lane-D receipt: no retained source-hash denominator, branch report, p50/p95, or peak RSS; the script can fall back to the interpreter | Host I/O/checksum comparison: **candidate host-executable**. It must be hardened to fail rather than fall back for native parity and to emit retained comparable samples/RSS/coverage receipts. |
| `doc/08_tracking/bug/mcdc_rt_hal_perf_harness_legacy_foreign_callback_2026-08-25.md` and `doc/08_tracking/bug/stage3_surface_freeze_segv_blocks_mcdc_rt_hal_verification_2026-08-25.md` | Performance receipt is source-fixed but unverified; self-hosted Stage 3 blocks MC/DC/RT-HAL gates | No performance, parity, or 100% branch-coverage claim is available | Host-executable C/Simple rows are **pending compiler recovery**; physical board-only leaves are separate unavailable/board-contract rows. |
| `doc/08_tracking/bug/text_branch_coverage_denominator_omits_unvisited_2026-08-26.md` | Compiler coverage inventory exists but all-owner text/rendering receipt is missing | Confirms denominator infrastructure is incomplete for broad branch claims | Add owner/source-hash/outcome receipts first; native C/Rust/SIMD/GPU coverage requires exact tool/profile/backend evidence. |

Checked-in `summary.txt` files are deliberately excluded as current verdicts:
the lane plan describes 10,720 zero-fail/skip/ignore/pending summaries as stale
Windows-origin historical receipts.  They cannot substitute for the missing
manifest.

## Required future evidence commands (not run)

Run these once only after the intended self-hosted binary and the worktree
revision are frozen; retain stdout/stderr, exit status, compiler SHA-256, host
identity, and every target source hash in a new manifest/receipt directory.
The sample runtime path below is valid only for a Linux x86_64 self-hosted
artifact at that exact path; select and record the matching target path and
hash on every other host.

```sh
RUNTIME=bin/release/x86_64-unknown-linux-gnu/simple
git rev-parse HEAD
sha256sum "$RUNTIME"
uname -a
SIMPLE_LIB=src "$RUNTIME" test test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl --mode=interpreter
sh scripts/check/check-stage-binaries-runnable.shs --verbose
sh test/perf/io_parity/run_io_parity_benchmarks.shs
```

`SIMPLE_NO_STUB_FALLBACK` is intentionally omitted above because the current
I/O parity script does not consume it; passing it would be ineffective. The
final command is only a checksum/startup benchmark candidate today; it is
**not** the required coverage proof.  Before any lane-D conclusion, replace its
interpreter fallback with a fail-closed native requirement, pin the C/Simple
file denominators and instrumentation profiles, execute shared success/error/
boundary/partial-I/O/EOF/timeout/unsupported/invalid-handle/dispatch cases,
and retain nonzero branch counts plus negative-control receipts.  Board-only
cases must have a separate QEMU/device matrix and must not inflate the host
branch percentage.

## Next action order

1. Add the deterministic deduplicated manifest and receipt schema before
   interpreting any historical count.
2. Reconcile the 19 historical gated rows as repaired, stale, unavailable, or
   currently failing; replay each currently failing row at most once.
3. Repair the mapped-code positive control and native concurrency proof before
   accepting aspect/facet lifetime or loader concurrency evidence.
4. Recover a current provenance-backed Stage 2/3 path, then perform the
   host-executable HAL parity/coverage lane; defer Stage 4 promotion until its
   required bootstrap receipt exists.

This ledger intentionally makes no pass/fail classification of live source and
does not modify or discard prior receipts.
