# Stage 2/3 manifest verifier reconstructs commands that the producer does not run

**Status:** Open; source mismatch identified, admission not exercised.

## Evidence

- `scripts/bootstrap/bootstrap-from-scratch.sh` computes the Stage 2 argument
  hash at lines 3443–3465 with ABI, plugin, kernel, coverage, composition,
  frontend-cache, and optional tool assignments. The reconstruction in
  `scripts/check/lib/bootstrap-stage3/manifest-verify.shs` at lines 616–640
  omits these assignments and adds `--compile-stack-mib`. Because the ordered
  arguments differ, the expected hash cannot equal the producer's hash.
- The producer's Stage 3 hash and executed transcript use
  `SIMPLE_FRONTEND_CACHE=1` (bootstrap script lines 3524 and 4521). The
  verifier reconstructs `SIMPLE_FRONTEND_CACHE=0` in both its expected hash
  and transcript check (manifest verifier lines 672 and 713). Its Stage 3
  reconstruction also omits the producer's ABI, policy, composition, and
  compatibility-cache assignments.
- `sh test/03_system/check/stage2_command_transcript_contract_test.shs`
  fails with `FAIL: Stage 3 transcript lost SIMPLE_ABI_POLICY=${simple_abi_policy}`.
  The test searches for an unquoted assignment although the producer passes
  `SIMPLE_ABI_POLICY="${simple_abi_policy}"`. A local diagnostic correction
  to that search exposed the next stale assertion: the test expects the
  nonexistent `bootstrap_stage3_transcript_args_sha256` helper in the
  verifier. The test still calls that removed helper near its end. These
  source assertions do not establish transcript or manifest admission.

## Impact and next repair

The current source reconstruction cannot prove an admitted Stage 2/3 build.
This is independent of the Stage 2 empty-CXX spawn failure documented in
`macos_stage2_empty_cxx_after_cocoa_owner_2026-09-27.md`; fixing that spawn
alone does not establish bootstrap admission.

Use one canonical ordered command specification for producer hash, executed
transcript, and verifier reconstruction, preserving exact environment and
argument values. Update the contract test to inspect the actual Stage 2 and
Stage 3 calls separately and to use the current transcript verifier API.
Then verify both a valid transcript and mutated env/argv rejection before
attempting another full bootstrap. No full bootstrap rerun is claimed here;
the feature's three-cycle verify/fix cap was already reached in this session.
