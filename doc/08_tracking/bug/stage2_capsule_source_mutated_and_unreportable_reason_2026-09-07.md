# Stage 2 sanity fails at `native-capsule-source-mutated` on hello world, and the reason is nondeterministically unreportable

**Status:** OPEN — diagnosed to the branch, NOT fixed. Two diagnosability defects
found alongside it are fixed (see "What was fixed").
**Component:** `src/compiler/80.driver/driver_aot_native_output.spl`,
`src/compiler/80.driver/driver_types.spl`,
`src/compiler/80.driver/driver_build/build_outcome.spl`
**Found via:** `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`
(aarch64-unknown-linux-gnu), 2026-09-07
**Supersedes the "one observation" note in**
`doc/08_tracking/bug/stage3_selfhost_parser_rejects_arrow_match_arms_2026-09-06.md:222-233`

## Symptom

Stage 2 **builds successfully** (`Build complete: 834 compiled, 0 cached, 0
failed`, `Time: 662.7s compile + 57.3s link = 720.0s total`) and then fails its
own sanity gate. The failing sub-check is the `hello_world_positional` probe of
`candidate_frontend_smoke`
(`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:357-397`).
Real error, from `stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
(**not** from `stage2-native-build.log`, which is a clean success log):

```
[build] native_cache 1/1 step 5/6 +3658ms dt=1ms complete
[build] native_compile 0/1 step 5/6 +3658ms dt=0ms scripts.check.cert.redeploy_gate.fixtures.hello_world
===== build outcome summary =====
OK=0
ERROR=1
ERROR: 1 unit(s)
  - scripts.check.cert.redeploy_gate.fixtures.hello_world
      reason: native-capsule-source-mutated:scripts.check.cert.redeploy_gate.fixtures.hello_world
===== end build outcome summary =====
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)
```

## Reproducer (3 seconds, no bootstrap)

```sh
C=<stage2 binary>
SIMPLE_BINARY=$C SIMPLE_BIN=$C SIMPLE_BOOTSTRAP_DRIVER=$C \
SIMPLE_FRONTEND_DELEGATE=$C SIMPLE_FRONTEND_DELEGATED=1 \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_EXECUTION_MODE= \
SIMPLE_NATIVE_BUILD_FORCE_WORKER=0 SIMPLE_BOOTSTRAP=0 SIMPLE_LIB=$PWD/src \
  "$C" native-build --backend llvm --runtime-bundle core-c-bootstrap \
  --entry-closure --cache-dir <fresh> --mode one-binary \
  scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output <out>
```

Reproduced on three independently built Stage-2 binaries:
`4d0c20ba36add1d5bb3407852480ad83143084bbf8c4ed42e8a36d5ad9feab7c`,
`39330f638ee8c632c47f4a19fb6d29e1c3253e66e97f9b5e3969df16c5039f30`,
`a11d1c069e8957287fc0e11eaf48181f75dd4d5fb00b0955ee4f3f33ee848a95`.

It is **not** lane-specific: it reproduces with a default `--output`, a default
cache dir, no `SIMPLE_CACHE_SCOPE`, with a relative AND an absolute entry path,
and with the fixture copied to an unrelated directory
(`reason: native-capsule-source-mutated:build.capsule_repro.sub.hw`). The
lane-isolation hypothesis in the 2026-09-06 record is therefore ruled out.

`--entry` instead of a positional entry "passes", but that is **not a control**:
`run_native_build_bootstrap` routes `--entry` (without `SIMPLE_BOOTSTRAP_STAGE4=1`)
to `run_rt_native_build`, i.e. the Rust seed FFI, which never executes this
pure-Simple code (`src/app/cli/bootstrap_main.spl:381-396`).

## Where the verdict comes from

`driver_native_collect_capsule_result_v1`
(`driver_aot_native_output.spl`) fires on either of two invariants:

```
if capsule.cache_source != "" and (
    capsule.source_identity == ""
    or driver_native_disk_source_identity(capsule.cache_source)
        != capsule.source_identity):
    return "native-capsule-source-mutated:{module_name}"
```

* `capsule.source_identity` = `sha256_text(source.content)` for the single
  `ctx.sources` entry whose `module_name` matches
  (`driver_types.spl`, `frozen_native_cache_source_identity_v1`), `""` if the
  match count is not exactly 1.
* `driver_native_disk_source_identity(path)` = `sha256_text` of
  `SourceFile.load(path).content`, `""` on `Err`.

## What is ruled out (evidence, not inference)

1. **Genuine on-disk mutation: NO.** Nothing writes the fixture during the run;
   the same failure occurs for a fixture copied to a private directory.
2. **Post-HIR source eviction (the obvious candidate): NO.** `evict_sources()`
   sets every `SourceFile.content` to `""` and is called from
   `driver_hir_pipeline_lowering.spl:433` (streaming HIR) and
   `driver_orchestration.spl:194` (low-memory). **Neither runs on this lane.**
   With `SIMPLE_COMPILER_PHASE_PROFILE=1` the repro emits no
   `phase3:streaming_source_reclaim`, no `phase2:source_reclaim` and no
   `phase1:streaming_preparse_source_reclaim`.
3. **Duplicate/alias module records: NO.** The same trace shows
   `phase1:load_sources:bulk:done logical=1`,
   `phase1:load_sources:owner_copy:done n=1`,
   `phase1:fingerprint:source idx=0 of=1 path=…hello_world.spl bytes=30` and
   `phase2:parse:closure:sources collected=1 unique=1`. Exactly one source, with
   its real 30 bytes, present at phase 1.
4. **The source-level semantics are correct.** Run interpreted under the Rust
   seed (`build/capsule-repro/hash_probe.spl`):

   ```
   len=30
   sha256_text(content)=2976a380c6fdfee06ca2b9452d65bc6a3514862c2a626d64e982503241ada42a
   sha256_text(empty)=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
   ```

   `sha256sum scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
   `= 2976a380c6fdfee06ca2b9452d65bc6a3514862c2a626d64e982503241ada42a` — the two
   sides of the comparison agree when the same code is interpreted.

**Verdict: FALSE POSITIVE, and compiled-code-specific.** Nothing mutates the
source; the compiled Stage-2 binary diverges from the semantics of its own
source in `sha256_text(source.content)` vs
`sha256_text(SourceFile.load(path).content)`. Which of the two sides is wrong is
NOT yet established — see the blocker below.

## Blocker: the reason is nondeterministically unreportable

The two hashes could not be obtained, because the diagnostic channel that would
carry them is itself broken.

`driver_native_collect_capsule_result_v1` was changed (landed, see below) to
report the two branches separately and to quote `cache_source`, `frozen=` and
`disk=`. On the two Stage-2 binaries rebuilt with that change, the summary
reports:

```
      reason: (none recorded — BUG in the producer: a non-OK unit must carry a diagnostic)
```

This is not caused by the longer message, and it is not the line-count retention
bound (`build_outcome_retain_diagnostics` returns a one-line blob unchanged).
**The same binary `4d0c20ba…`, with the identical command, printed the real
`native-capsule-source-mutated:…` reason earlier the same day and prints
`(none recorded)` now.** The loss is nondeterministic on a fixed binary.

`reason_block_for` only emits that line when a record MATCHING the path exists
with `diagnostics == ""`, so `outcomes.record(...)` did run — i.e.
`driver_native_record_module_failure` was reached with an empty `detail`, or its
`detail` was lost between the argument and the stored field.

An unconditional `print` added as the first statement of
`driver_native_record_module_failure` did **not** appear in the output of either
rebuilt binary, on the bootstrap lane or on a direct run, even though `strings`
confirms the literal is present in the binary and `print` demonstrably works
elsewhere in the same file (`print outcomes.summary()`). That probe was reverted
rather than shipped, because a statement that provably emits nothing is dead
code — but the observation stands and is the sharpest lead: **leading statements
of this function appear not to execute in the Stage-2-compiled compiler.**

## Also found, not fixed

Duplicate top-level definitions in `driver_aot_native_output.spl`, introduced by
`848f626638b` ("surgical extraction of PR #235"): `driver_native_disk_source_identity`
twice (bodies identical) and `driver_native_module_source_identity` twice
(bodies DIFFERENT — one reads the SoA owners via
`driver_native_frozen_source_lookup`, the other iterates `ctx.sources`). Neither
is on the failing path, so this is not the cause here, but a merge artifact of
that shape will bite something.

## What was fixed (separate commits)

1. The stage-2 failure diagnostic read only `stage2-native-build.log` while
   `stage2_status` is also set by the sanity gate, the receiver check and the
   admission publish. `check-stage-log-diagnosable.shs --log` is now repeatable,
   scans every candidate and NAMES the one carrying the reason;
   `bootstrap-from-scratch.sh` passes all eight stage-2 logs. Proven in situ on
   a real bootstrap run.
2. `native-capsule-source-mutated` now names WHICH invariant fired and quotes
   `cache_source`, `frozen=` and `disk=`; `source-identity-empty` /
   `source-identity-mismatch` likewise.

## Next step for whoever picks this up

The reason plumbing must be made reliable before the capsule hashes can be read.
The cheapest route is probably not `print` (see above) but writing the verdict to
a file with `rt_file_append_text` from inside
`driver_native_collect_capsule_result_v1` itself, on a fresh Stage-2 build.
