# Stage2 compiler-test matrix fails at head: seed-vs-stage2 native divergence

Date: 2026-10-12. Lane: release_phase3 self-host bootstrap campaign, worktree
`/home/yoon/dev/simple-release-phase3-20261011`, head 099c81b599b + docs commit
063e6738486. Status: OPEN (P1). Blocks Step 1 acceptance
(`--full-bootstrap --stop-after-stage2` → `VERDICT — ABORTED: stage=stage2-compiler-tests`).

## Reproduction

Canonical receipt-free lane:
```
env -u SIMPLE_BOOTSTRAP -u SIMPLE_BOOTSTRAP_STAGE4 \
  LLVM_SYS_231_PREFIX=<llvm-23.1.2> SIMPLE_LLVM_PATH=<libLLVM-23.so> \
  BOOTSTRAP_STAGE2_TEST_DELEGATE=0 SIMPLE_NO_BOOTSTRAP_DELEGATE=1 SIMPLE_NO_STUB_FALLBACK=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 --backend=llvm --mode=dynload \
  --strategy=full --jobs=full --keep-going
```
Stage 2 native build PASSES (`Cache: reused 1239 modules; rebuilt 2` on retry;
all frontend smoke / struct-receiver / phase2-manifest sanity gates PASS).
The subsequent **stage2 compiler tests (phase verification matrix,
strategy=full profile=full)** fail. Reproduced independently by a second lane
(`/tmp/rp3-main`, cranelift backend, slim profile, different receipt policy):
identical FAIL set (`compiler_cli_build`, `test_runner_build`,
`stage2_tool_workers`), so this is a head-level frontier, not lane-local.

## Failing tasks (this lane, full/full matrix)

- `mcp_build` FAIL — MIR lowering against the SCV snapshot:
  - `unresolved method call: trim` (first lowered to const-0 placeholder,
    then a hard MIR error) in `lib.common.json.array_ops`;
  - `for-in over non-array iterables is not supported by native codegen yet
    (#143); collection mir type: Tuple` at
    `src/lib/common/json/array_ops.spl:479:25` — the inner loop
    `for item in nested` where `nested = json_to_array(elem)` has inferred
    (non-annotated) type, lowered as Tuple.
- `test_runner_build` FAIL — `MIR lowering error: record collection payload
  owner is unavailable in the consumer` (last module
  `lib.nogc_sync_mut.simd_crypto`).
- `compiler_cli_build` FAIL — no compile error; the log ends in the watchdog
  receipt: killed by the 7200 s campaign deadline under CPU contention (20-core
  host shared with the parallel rp3-main lane). Needs a re-run with less
  contention to get a clean signal.
- `module_compile_campaign` INCOMPLETE (same deadline).

Evidence: `.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`,
`.../logs/{mcp_build,test_runner_build,compiler_cli_build}.log`,
`.../rejection.env`.

## Seed-vs-stage2 discriminator

Minimal entry calling `json_array_flatten(json_array([...]))`
(`build/step1/repro/repro_main.spl`):
- Rust seed (`src/compiler_rust/target/bootstrap/simple`) native-builds the
  closure cleanly (4 modules, 0 failed).
- The stage2-admitted compiler (sha256
  4a49280ac268ebf647310e8be3d3c2ad7f34df32289c26a20934aa6c350664b1) fails the
  same sources inside the verifier harness with the errors above.
- A standalone re-run of the stage2 binary outside the verifier aborts earlier
  on `SCV-E-ADMISSION: derived-composition-identity-mismatch` (the harness
  binds composition identity the ad-hoc env does not reproduce), so the
  MIR-error comparison stands only for the harness-run pair.

## Relation to known families

Matches documented open strictness families in
`doc/08_tracking/bug/phase2_matrix_strict_stage2_error_family_2026-10-09.md`
(for-in #143 / receiver-identity cascades; 2026-10-11 addendum: HIR match-arm
payload typing, workaround in PR #2999 on `work/release-llvm-fixes-20261011`,
compiler-side fix still open) and the payload-owner family tracked in
`result_err_record_owner_erased_2026_10_11` / `enum_static_receiver_owner_erasure_2026_10_11`.
This run shows the families still fire at head 099c81b5 in the
receipt-gated stage2 matrix, now reachable end-to-end once the bootstrap
infrastructure issues (see `stage2_cache_idle_writer_repair_unavailable_2026-10-12.md`)
are cleared.

## Campaign state notes (2026-10-12)

- Infrastructure repairs applied this session (env only, no source changes):
  admitted LLVM 23.1.2 prefix; `--invalidate-cache=stage2`; stale
  `stage2-native-cache.writer` lock archived (in-band repair unavailable by
  design); SCV source-inventory cold-rebuilt after exactly one stale row
  (`session_authority_v2.spl`) was found in generation 97
  (evidence: `build/step1/gen97-drift-check.txt`, archived inventory under
  `build/step1/scv-evidence/`); long runs launched under `setsid` after an
  external SIGTERM from the agent-shell session killed one attempt.
- Stage 2 admission receipt, parent receipts, and runtime capsule were
  published and remain on disk; per the bootstrap's own warning, do NOT resume
  Stage 3 from this output until the compiler-test failure is understood.

## Next actions

1. Re-run the matrix with exclusive CPU (parallel lane stopped) to get a clean
   `compiler_cli_build` signal (timeout vs real error).
2. Compiler lane: fix the match-arm payload-typing / receiver-identity root
   cause (not the PR #2999 source workaround) and the record payload-owner
   consumer check; re-verify with `build/matrix-probes/` minimal repros.
3. Then re-run Step 1; on PASS proceed to planner admission + stage3
   construction (jobs=1) and the Phase 3 verification gate.
