# Resource-budget env knobs void the native object-cache identity (module scope)

Date: 2026-11-13
Branch: work/cache-identity-rss-20261113 (base origin/release/1.0.0 @ f790f7f266e)

## Symptom

Stage-2 bootstrap matrix campaign (`/private/tmp/boot-main-20261112`), pinned source
`pinned-f9dd7ada7645`, compiler snapshot
`197b4e93670dd57c9a2da298069ad95b369dc8f75dff57b9a2ced98631c00289`: two
config-identity directories appeared under

```
.../stage2-compiler-tests/aarch64-apple-darwin/cache/compiler-tools/stage2/197b...2289/
    bfe668dca92ed8aa79197e24c62245e4e301bb81e0cfa221d375178d8d2f6385/   (1297 warm full-cli/hir/*.parser-v4.hir)
    6d00fcea34f5730323e221010e6e607774f164b9437aafbc3b5d83682bbd9dd0/   (cold: "Cache: reused 0 modules; rebuilt 1672")
```

The run that produced `6d00fcea` logged different resource-budget env values
(`verification_frontend_policy=SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=...`; the sibling
run had a different KiB value), which suggested the cache identity was folding
resource-budget knobs.

## Where the identities are computed

Two distinct identities were investigated:

1. **Bootstrap tool-cache dir identity** — `bootstrap_phase_c_tool_input_identity`
   (scripts/bootstrap/phase-c-backend-commands.shs:13-17), called from
   bootstrap-phase-verification.shs:1755; the dir is built at :2634
   (`compiler-tools/<phase>/<snapshot_sha>/<tool_input_identity>`) and is passed to the
   tool rows as `--cache-dir` (hence `full-cli/hir`, `full-cli/default`, ... under it).
   Inputs: `sha256(runtime_identity, target_c_identity, target_c_source_sha, backend)`.
2. **In-compiler module object-cache identity** —
   `native_build_module_environment_snapshot_fingerprint_v1`
   (src/compiler/80.driver/cache/native_build_environment_identity.spl:244). Its digest
   is folded into `options_identity` → `NativeModuleConfigFactV1`
   (driver_aot_native_output.spl:2120) and into the cache scope dir
   (`driver_native_build_cache_scope`, driver_aot_native_output.spl:2123-2126). The
   complete capture folds **every present `SIMPLE_*` env var**; the module projection
   then drops a known scheduling/observability exclusion list.

## What actually changed between the two runs (hash reproduction)

The `tool_input_identity` inputs were reproduced exactly (sha256 over the same four
lines) for both runs and match the on-disk dir names:

- run1 (`bfe668dca92e...`): `target_c_tool_path=/opt/homebrew/Cellar/llvm/23.1.1_1/bin/clang-23`
- run2+ (`6d00fcea34f5...`): `target_c_tool_path=/usr/bin/clang`

The resolved C compiler and the managed-tool record (`target-managed-tools.env`, whose
per-tool `requested=` PATH spelling also changed) differ because the two campaign
launches ran with **different ambient PATH/CC**: run1's shell resolved `clang` to
Homebrew LLVM 23.1.1, run2's resolved `/usr/bin/clang` (Apple clang). Those are semantic
inputs — a different C compiler produces different runtime objects — so folding them is
correct, and `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` never entered this identity at all.
The 1297-entry HIR cache was lost because `--cache-dir` moved to a new, cold directory.

Conclusion for identity #1: **not a resource-knob leak**; the split was an ambient
toolchain-resolution change between campaign launches (residual risk below).

## The real resource-knob leak (identity #2)

The module projection excluded `SIMPLE_MIR_SHARD_WORKER_KB`, `SIMPLE_SHARD_MEM_CLAMP`
and `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` (c458ffe5cbc) but **not** their siblings that
the phase-C row environment also carries with campaign-varying values
(scripts/bootstrap/phase-c-backend-commands.shs:66-69, exported per run by
`bootstrap_phase_c_apply_frontend_policy` and the tree-RSS watchdog):

- `SIMPLE_PARSE_SHARD_WORKER_KB` — parse-shard pool memory budget
  (src/app/cli/native_build_main.spl:784)
- `SIMPLE_HIR_SHARD_WORKER_KB` — HIR/file-worker pool budget (native_build_main.spl:975-976, 1716)
- `SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP`, `SIMPLE_PROCESS_TREE_RSS_DECLARED_JOBS`,
  `SIMPLE_PROCESS_TREE_RSS_RECEIPT`, `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB`,
  `SIMPLE_PROCESS_TREE_RSS_CAP_KIB` — watchdog coordinates; only
  shard_mem_clamp.spl:733,747 reads the cap/mode, to size the worker pool
- `SIMPLE_BOOTSTRAP_RSS_CAP_MODE` — enforce/off clamp mode (shard_mem_clamp.spl:703-711)
- `SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS` — observer budget, no compiler reader

All are pure resource/scheduling knobs: they choose how many processes run and how
memory is clamped, never what any process emits. Because the complete capture folds
every present `SIMPLE_*` var and the projection did not drop these, any retuned
campaign run got a private `environment=<digest>` object scope and 0 module reuse —
inside the *same* tool-cache dir, so the split-dir evidence was not even required to
lose the cache.

## --threads determinism reasoning (kept hashed)

`SIMPLE_NATIVE_BUILD_THREADS` stays in the module identity (unchanged; excluded only
under `SIMPLE_MIR_SELECTIVE=1`, where each physical job owns a fresh lowering owner —
native_build_environment_identity.spl:255-259). The repo's canonical-hash policy treats
worker counts as non-semantic for object identity: "the number of admitted sibling
processes cannot change its object identity" (:256-257) and MIR sharding "only
choose[s] WHICH process emits a module" (:263-267); a cached object is still admitted
only by its capsule's complete MIR witness. The excluded knobs are strictly weaker than
thread count — they only size pools/clamp workers (never even a deterministic
work split any consumer could observe). Semantics-affecting flags (`SIMPLE_ABI_POLICY`,
`SIMPLE_NATIVE_CPU`, codegen/backend options, `SIMPLE_NATIVE_ARENA_DECLS`, ...) remain
hashed; verified below.

## Fix

`src/compiler/80.driver/cache/native_build_environment_identity.spl`
(`native_build_module_environment_snapshot_fingerprint_v1`):

- Added `SIMPLE_PARSE_SHARD_WORKER_KB` and `SIMPLE_HIR_SHARD_WORKER_KB` to the existing
  MIR-shard exclusion chain (:271-272).
- Added the watchdog/RSS coordinates
  (`SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP`, `SIMPLE_PROCESS_TREE_RSS_DECLARED_JOBS`,
  `SIMPLE_PROCESS_TREE_RSS_RECEIPT`, `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB`,
  `SIMPLE_PROCESS_TREE_RSS_CAP_KIB`, `SIMPLE_BOOTSTRAP_RSS_CAP_MODE`,
  `SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS`) to the observability/RSS-ceiling
  exclusion group (:336-342), with the rationale in the comment (:320-327).

The complete capture (`native_build_environment_snapshot_fingerprint_v1`) still records
every one of these for admission/no-op evidence; only the module projection drops them.

## Spec

`test/01_unit/compiler/driver/native_module_environment_projection_spec.spl`:

- The block "ignores per-run observability sinks and the external RSS ceiling" asserted
  (since fef2112684e, 2026-10-19) that `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` *moves* the
  module scope; that has been stale since c458ffe5cbc (2026-10-22) excluded it. Updated
  the assertion to match the implementation: retuned budgets/worker-KB/RSS coordinates
  share the bare baseline scope, a semantics flag still moves it, and the complete
  capture still records the knobs.

## Verification

- No Simple runtime in this worktree can execute current sources (`bin/simple` absent;
  only seed `release100-7a0e6fe516f-20261031` and binaries up to v1.0.0-rc.1, which
  fail to parse/run this tree), so `bin/simple check` / interpreter specs could not run
  here. Verification was:
- `scripts/bootstrap/cache-identity-model-check.py` — a faithful Python model of both fingerprint
  functions, run against the pre-change and post-change exclusion sets: before, changing
  worker-KB budgets or watchdog coordinates moved the module digest; after, retuned
  resource runs share the baseline scope while a semantics flag and `--threads` still
  move it, and the complete capture still distinguishes the runs. RESULT: PASS.
- Exact sha256 reproduction of both observed config-identity dir names from the
  recorded receipt fields (see above), proving which inputs moved.
- Manual repro for a runtime-equipped worktree:
  `SIMPLE_PARSE_SHARD_WORKER_KB=3800000 simple test test/01_unit/compiler/driver/native_module_environment_projection_spec.spl --mode=interpreter --unstable --no-cache --no-db --no-session-daemon --sequential`
  (expect all green; before the fix the new budget assertions fail).

## Residual risk / follow-ups

1. The *observed* dir split was ambient toolchain resolution (clang via `command -v`
   under the launching shell's PATH), not a hash bug. Folding the C toolchain is
   semantically right, but selection should be pinned to the admitted managed tool
   authority instead of ambient PATH, or every campaign launch from a differently-ordered
   PATH silently splits the tool cache again (and, worse, can silently build the C
   runtime with Apple clang instead of the pinned LLVM 23.1.x on macOS — Unix rows only
   validate `grep -qi 'clang version'`).
2. The in-compiler identities still fold any *unknown* `SIMPLE_*` var present in the
   environment. New resource knobs must be added to the exclusion list by hand; the
   worker-HIR profile's admitted list (src/app/cli/worker_hir_profile_v1.spl:139-179) is
   a good cross-check source for row-carried knobs.
