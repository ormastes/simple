# Phase 2 (stage2) — gate definition, ranked blockers, load-bearing test set

Date: 2026-08-23. Scope: the adhoc bootstrap pipeline of
`doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` §27.
Everything below is read out of the scripts, not from memory. No compiler code
was changed by this investigation.

## 1. The gate, read from the driver

Driver: `scripts/bootstrap/bootstrap-from-scratch.sh` (not `scripts/setup/`).
`bin/simple build bootstrap` only prints HELP; it does not build. By default the
driver `exec`s `scripts/bootstrap/bootstrap-strategy.sh --strategy=<adhoc|normal|full>`,
which re-enters this same engine with `SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1`.

### 1.1 What produces stage2

One `native-build` invocation of the **stage1/seed** binary
(`${stage2_seed_absolute}`, the frozen runtime-authority copy), transcribed
through `bootstrap_stage3_run_transcribed` (script L2166-2192):

```
$SEED native-build --target $PLATFORM --backend llvm \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads $jobs \
  --cache-dir <stage3-provenance-dir>/stage2-native-cache \
  --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path <stage2-runtime-authority> \
  -o build/bootstrap/stage2/$PLATFORM/simple
```

Env: `SIMPLE_BOOTSTRAP=1`, `SIMPLE_NATIVE_BUILD_RUST=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_NO_DEPRECATED_WARNINGS=1`,
`SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256`, `LIBRARY_PATH`, `SIMPLE_BINARY=$SEED`.
The identical argv is separately hashed into `stage2_build_args_sha256`
(L2101-2119) so the recorded receipt and the real invocation cannot disagree.

**Inputs:** the seed binary; the frozen runtime authority directory (snapshotted
and `cmp`-verified before *and* after the build); the whole `src/compiler`,
`src/app`, `src/lib` source closure reachable from
`src/app/cli/bootstrap_main.spl` under `--entry-closure`; the `core-c-bootstrap`
runtime bundle; a private HOME/TMPDIR/cache under the stage3 provenance dir.

**Artifact:** `build/bootstrap/stage2/<triple>/simple`. A candidate that fails
sanity is **renamed to `simple.rejected`**, never deleted, so it stays off every
downstream `-x` guard while remaining available for post-mortem.

**Receipt-free lane:** `--full-bootstrap --stop-after-stage2 --mode=dynload`
(L357-371, L396-403) is the *sole* lane that needs no planner receipt; it sets
`bootstrap_reason=stage2-trust-root-refresh`. Any other lane requires a
`--bootstrap-receipt` targeting `//bootstrap:stage2`.

### 1.2 What "stage2 success" actually is — three gates, not a link

A linked binary is **not** phase 2. Stage 2 is admitted only after:

1. `stage2_status == 0` **and** `-x $stage2_bin`.
2. `bootstrap_stage_sanity` (script `bootstrap_stage_sanity()`), which scrubs the
   entire environment and then asserts, all on the candidate itself:
   - `--version` equals `simple-bootstrap $(cat VERSION)`, where the expected
     string is **derived**, and cross-checked against
     `src/app/cli/bootstrap_identity.spl`; disagreement or an unreadable VERSION
     is `sanity_status=error`, never a pass. (This gate was previously
     unsatisfiable and silently so — release `9a3f6051996` bumped VERSION and not
     the hardcoded literal.)
   - a **negative control**: `run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl`
     must be *rejected* with rc 1 and the exact diagnostic — proving the binary
     reached its own argv dispatch and is the bootstrap CLI. Do not "fix" this
     into a working `run`.
   - `candidate_frontend_smoke` **twice**: once with `CANDIDATE_FRONTEND_BOOTSTRAP=0`
     and again with `=1`, the exact configuration stage 3 invokes it in. The
     single-pass version admitted, on 2026-08-09, a stage2 that could not lex a
     two-line file and then ran unbounded (444 MB log / 32 GB RSS).
   - the candidate's sha256 before and after must match.
3. The struct-receiver / runtime-capability proof (`stage2-receiver.env`,
   gated by `scripts/check/check-bootstrap-stage2-struct-receiver.shs`), again
   re-hashing the binary around the run.

Only then is the binary copied to `stage2-admitted/simple` with
`admission.env`, and it is that **admitted, frozen** copy — not
`build/bootstrap/stage2/.../simple` — that stage 3 runs as `SIMPLE_BINARY`.

### 1.3 What the `cmp` steps compare (correction)

There is **no stage2-vs-stage3 binary comparison**. The `cmp -s` calls in the
driver compare *snapshots*, and they are integrity gates, not equality proofs:

- `runtime-origin-before.txt` vs `-after.txt` vs `runtime-admitted.txt` — the
  runtime authority was not mutated while being copied (L1987).
- `runtime-before-stage2.txt` / `runtime-after-stage2.txt` vs the admitted
  snapshot — "frozen runtime authority changed during Stage 2" is fatal (L2163,
  L2196-2200).
- `stage3-source-inputs-before.txt` vs `-after.txt` (L2285, L2305) — the source
  tree did not change under the stage-3 build.

The genuine **fixpoint** assertion lives in
`scripts/check/check-bootstrap-stage3-selfverify.shs` check **A12**, and is
*opt-in*: only when `--fixpoint-binary PATH` is supplied does it assert that
re-running stage3 on the stage3 entry is byte-identical to stage3
(`fixpoint_stage3_recompile_not_byte_identical`). Without it the script notes
`stage3_strict_fixpoint=not_supplied` and passes. Stage 4 explicitly does **not**
assert a fixpoint at all — `check-bootstrap-stage4-selfverify.shs:21-37` states
the property stage 4 claims is a *capability* delta (full CLI: `lint` accepted by
stage4, rejected by its stage3 parent), and records
`stage4_fixpoint_asserted=false_known_gap`; its F5 must-FAIL fixture is a stage4
that is byte-identical to its parent.

**So: "3-stage self-compilation verification" asserts provenance + sanity +
capability, and asserts byte-identity only if the caller opts in.** Any plan
that treats `cmp stage2 stage3` as the phase-2 gate is aimed at something the
scripts do not do.

## 2. Ranked blockers between here and stage2

Ranked by whether they can stop stage 2 at all, then by proximity.

**B1 — stage1 has never reached step 6/6; it is still the phase-1 gate.**
Evidence: §27 "Phase 1 (stage1 bootstrap) state", current run11b, worktree
`stage1-clean13`, seed `e5f12c93`, tree `a6233953eca`. Until the seed completes
its own native-build there is no `${stage2_seed_absolute}` to invoke, and every
item below is unreachable. Owner: the existing Phase-1 lanes.

**B2 — a stage2 that links is not a stage2 that is admitted.** §1.2 above: three
independent gates run *after* the link, two of them executing the candidate.
The 2026-08-09 incident (`stage2_binary_lexer_reads_every_source_as_empty_infinite_parser_loop_2026-08-09.md`)
is the precedent: a cleanly linked stage2 that could not lex. A fixture binary
linking green and then SEGV-ing is the same class. Planning that ends at "links"
under-scopes phase 2 by three gates.

**B3 — 83 codegen-emitted runtime symbols are undefined in the C runtime
archive.** Records: `c_runtime_missing_83_codegen_runtime_symbols` (§27 open
items) and `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.
Mechanism, already diagnosed: the native link tolerates the undefined symbol
("Unresolved symbol preview: …"), the NULL GOT slot becomes SIGSEGV at first
call. `-fsyntax-only` never links so `check-c-runtime-compiles-push.shs` cannot
see it; the extern ratchet classifies Simple `extern` declarations, not
codegen-emitted calls. This is the mechanism that turns a green link into a
SEGV, i.e. it is B2's most likely concrete cause. Gate:
`scripts/check/check-no-unresolved-runtime-symbols.shs` (ADVISORY, honestly RED
for exactly this reason).

**B4 — native-build throughput/§memory, not correctness, is what has been
consuming the runs.** Open Phase-1 records:
`bootstrap_main_native_build_stalls_after_source_closure`,
`native_build_phases_after_parse_single_threaded`,
`native_build_frontend_not_incremental`,
`native_build_object_cache_never_persists_entries`,
`phase3_hir_import_materialization_time_rss`. Stage 2 compiles a strictly larger
closure than stage 1's (three `--source` roots under `--entry-closure`), so each
of these costs more at stage 2 than at stage 1. Also: `kill_simple_monitor.shs`
kills any run without `SIMPLE_TIMEOUT_SECONDS=0` — a mandatory env for a
multi-hour stage2.

**B5 — stage1 executes entirely on the tree-walking interpreter.** The JIT bails
at `compiler_services.spl:168`; no compiled code runs during stage1 (§27, lane
`seed_jit_coverage_self_hosted_compiler_2026-08-21.md`). This does not block
correctness but sets the wall-clock floor for both phases.

**B6 — entry-closure completeness.** `stage2_split_impl_modules_missing_from_entry_closure`
is stage-2-specific by name: `--entry-closure` from `bootstrap_main.spl` must
reach every split impl module or stage2 links against a hole. Adjacent:
`stage1_untyped_return_reintroduced_by_clobber_llvm_backend`,
`stage1_lexer_hir_fatals_eprint_and_generic_len_helper`.

**B7 — the must-pass hook is circular.** `check-push-must-pass` demands a
bootstrap fingerprint producible only by the bootstrap it gates —
`check_push_must_pass_requires_unobtainable_bootstrap_fingerprint_2026-08-22.md`.
Not a build blocker; a landing blocker for anything claiming phase-2 evidence.

### 2.1 Overturned premise (measured today)

`sh scripts/check/check-stage-binaries-runnable.shs` on `origin/main`
(`7a0457b3e3b`) reports:

```
ERROR — nothing was checked (no tracked bootstrap stage binary found under .../bootstrap)
```

with `selftest 6/6 fixtures correct`. `git ls-files bootstrap` returns **0
entries**, at the working tree *and* at `origin/main`. The four tracked stage
binaries that were documented as SEGV-ing are **no longer tracked at all** — the
guard's state is ERROR (exit 2), not FAIL. "All four tracked stage binaries SEGV
on hello-world" is therefore stale as a *current* reading; it remains valid as
the historical record of the artifacts that were removed. Note also that
`... | tail -5; echo rc=$?` prints `rc=0` — the pipeline's status is `tail`'s.
Read the verdict line, never the exit code through a pipe.

## 3. Load-bearing test set

Most of the ~21k specs are irrelevant to bootstrapping. These gate phase 2:

**Shell contract tests for the driver itself** (`test/01_unit/scripts/`) — these
test the exact machinery in §1: `bootstrap_from_scratch_rust_authority_contract_test.shs`,
`bootstrap_stage2_struct_receiver_gate_test.shs`,
`bootstrap_stage3_current_acceptance_contract_test.shs`,
`bootstrap_stage3_directory_snapshot_streaming_test.shs`,
`bootstrap_planner_admission_bound_contract_test.shs`,
`bootstrap_cache_policy_test.shs`, `bootstrap_fingerprint_tmp_contract_test.shs`,
`bootstrap_progress_watch_tree_test.shs`,
`bootstrap_resume_stage4_from_admitted_contract_test.shs`.

**Bootstrap CLI / driver pipeline specs:**
`test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl`,
`test/01_unit/app/cli_native_build_main_contract_spec.spl`,
`test/01_unit/app/native_build_worker_minimal_runtime_import_contract_spec.spl`,
`test/01_unit/os/native_build_compiler_provenance_spec.spl`,
`test/03_system/compiler/compiler_driver_system_spec.spl`,
`test/03_system/compiler/driver_api_heavy_path_spec.spl`.

**Stage-binary runnability / SEGV class:**
`test/03_system/compiler/stage3_segfault_fix_spec.spl` (and its
`test/system/` mirror), `test/03_system/compiler/bootstrap_stage3_real_body_spec.spl`,
`test/system/simpleos_native_build_entry_closure_spec.spl`.

**Acceptance / gate specs:** `test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl`,
`test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl`,
`test/03_system/check/stage4_memory_gate_spec.spl`,
`test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl`,
`test/03_system/tools/bootstrap_mcp_spec.spl` (the pipeline's terminal MCP
`initialize` + `tools/list` step).

**Guards that are gates, not tests:**
`check-bootstrap-stage2-sanity-gate.shs`, `check-bootstrap-stage2-struct-receiver.shs`,
`check-bootstrap-stage3-selfverify.shs` (pass `--fixpoint-binary` if a fixpoint
claim is wanted), `check-bootstrap-preflight.shs`,
`check-no-unresolved-runtime-symbols.shs` (RED, B3),
`check-stage-binaries-runnable.shs` (ERROR, §2.1).

Everything else red is out of scope for phase 2 and must not be allowed to
consume phase-2 fix capacity.

## 4. Reporting caveats — do not build a blocker list on these

- The test DB is incoherent: `Total 770 / Passed 0 / Failed 0`.
- A post-run `runtime_file_rename` error forces `rc=1` on runs that passed.
- A `@cover` preflight gate manufactures hundreds of phantom failures, emitting
  a fully formed `Results:` line with **zero specs executed**. Bypass with
  `--no-cover-check`.
- Therefore: verify every verdict against `Files: N discovered, N executed`,
  `Time:`, and per-spec `PASS`/`FAIL` lines. Never `Results:` and never an exit
  code alone — and never an exit code read through a pipe (§2.1).
