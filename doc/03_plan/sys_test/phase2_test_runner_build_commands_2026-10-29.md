# Phase 2 test CLI build commands

Run from `/tmp/simple-release-1.0.0-phase2-combined-20261029`. Substitute the admitted Phase 2 compiler, its exact SHA-256 digest, the matching runtime authority, and an isolated session output root. These commands are prepared instructions; they have not been executed by this review lane.

**Qualification prerequisite:** the canonical verifier requires this source tree to match the compiler's admitted source inventory. An admitted compiler built before the runner patch does not satisfy that condition. Do not run the canonical commands below against modified sources and then bypass their source mismatch failure. They apply only after admitting the compiler for these sources, or against its matching original source tree.

```sh
sh scripts/bootstrap/bootstrap-phase-verification.shs \
  --phase=stage2 \
  --backend=llvm \
  --compiler="$runner_phase2_compiler" \
  --compiler-sha256="$runner_phase2_sha256" \
  --strategy=normal \
  --hash-policy=canonical \
  --work-root="$runner_verification_root" \
  --cache-root="$runner_verification_cache" \
  --runtime-path="$runner_runtime_authority" \
  --source-root=/tmp/simple-release-1.0.0-phase2-combined-20261029 \
  --timeout-seconds=900
```

The complete canonical Linux post-bootstrap matrix wraps that verifier, applies resource caps, verifies the frozen command-owner receipt, and then exercises the resulting binaries:

```sh
sh scripts/bootstrap/run-linux-phase2-tests.shs \
  --backend=llvm \
  --compiler="$runner_phase2_compiler" \
  --compiler-sha256="$runner_phase2_sha256" \
  --runtime-path="$runner_runtime_authority" \
  --work-root="$runner_post_phase2_root" \
  --source-root=/tmp/simple-release-1.0.0-phase2-combined-20261029 \
  --strategy=normal \
  --timeout-seconds=900
```

Choose one entrypoint; do not run both unchanged and repeat the same verification. The post-bootstrap wrapper clears its own stale compiler-tool output directory, so its work root must be session-owned.

## Exact compiler argv used by the verifier

`scripts/bootstrap/phase-c-backend-commands.shs:49` supplies these shapes under the verifier's validated environment:

```sh
"$runner_phase2_compiler" native-build \
  src/app/cli/_CliMain/main_and_help.spl \
  --backend=llvm --low-memory --timeout "$runner_internal_timeout" \
  --threads "$runner_build_threads" -o "$runner_cli_output"

"$runner_phase2_compiler" native-build \
  src/app/test_runner_new/main.spl \
  --backend=llvm --low-memory --timeout "$runner_internal_timeout" \
  --threads "$runner_build_threads" -o "$runner_test_output"
```

These argv are explanatory, not substitutes for the verifier's authority setup. Phase 2 uses a positional entry and its compiler-native build surface; the later-stage `--source`/`--entry-closure` command is a separate branch in the verifier.

## Required provenance and environment

The Phase 2 compiler's directory must contain a regular `admission.env`. The verifier reads `source_snapshot_sha256`, `runtime_authority_path`, `runtime_snapshot_path`, `runtime_snapshot_sha256`, `tool_authority_path`, and `tool_authority_sha256`; it verifies referenced snapshot hashes and binds current target C inputs. Preserve the patched worktree diff alongside the parent compiler's admitted source identity.

The verifier sets the managed native tool/runtime authority paths and digests, `SIMPLE_MANAGED_NATIVE_TOOLS=1`, `SIMPLE_RUNTIME_PATH`, `SIMPLE_PROJECT_ROOT`, isolated native/frontend/HIR/runtime caches, target, thread count, and resource policy. Runtime bundle must remain core-C bootstrap, ABI policy v1, and RISC-V vector override disabled. It resets stage-3/stage-4 route variables for Phase 2.

Outputs are `outputs/compiler-tools/stage2/<compiler-hash-prefix>/<tool-input-hash-prefix>/simple_cli` and `simple_test_runner`. Require the frozen `simple-bootstrap-command-owners-v3` receipt, backend and phase match, matching executable paths and hashes, and real verdict-producing execution before accepting them. A seed log claiming a one-binary fallback does not establish Phase 2 or full-CLI qualification; never use the seed as the acceptance runtime.

## Modified target sources with an older admitted producer

Compiler origin and application input are distinct identities. `phase2-runtime-binding.shs resolve` deliberately enforces same-source Phase 2 qualification; `bootstrap-phase-verification.shs` also derives its target-source receipt field from that admission. Relaxing only the source comparison would mislabel the resulting product.

For a scoped diagnostic application build, first validate the producer/runtime binding against the producer's original frozen source root. Independently snapshot the modified target tree before and after the direct compiler invocation above, preserve compiler/admission/runtime/tool hashes and exact argv/environment, and hash the resulting executable. Label the result a derived diagnostic application built by the admitted Phase 2 producer, never a current-source Phase 2 qualification or canonical Stage 2 PASS. Do not rewrite or copy an admission to claim new source identity.

The repository's broader typed diagnostic route is `bootstrap-provisional-phase3-phase4.shs`, which accepts separate source-authority and original-source-snapshot pins plus producer/Hello, runtime, tool, SCV, and manager authorities. That route requires its complete authority setup; it is not a flag that bypasses canonical binding.
