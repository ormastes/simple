# Push advisory gate destination inventory — 2026-09-25

Generated from the current eight-column `must_check_gates.sdn` worktree, which is dirty in another active lane. `Workflow mentions` is a text search and **does not prove a required job executes the gate**. Every advisory row has `ci_job=-`; an empty other-row/mention column is a mapping gap, not proof that the check never runs.

| Push advisory ID | Command script | Other registry rows | Workflow mentions |
|---|---|---|---|
| push-deployed-closure-dedup | `scripts/check/check-deployed-closure-dedup.shs` | — | — |
| push-ui-slim-closure | `scripts/check/check-ui-slim-closure.shs` | push-ui-slim-closure-tui-entry (push), push-ui-slim-closure-cli-entry (push) | rust-bootstrap-multiplatform.yml, code-idiom-gates.yml |
| push-ui-slim-closure-tui-entry | `scripts/check/check-ui-slim-closure.shs` | push-ui-slim-closure (push), push-ui-slim-closure-cli-entry (push) | rust-bootstrap-multiplatform.yml, code-idiom-gates.yml |
| push-ui-slim-closure-cli-entry | `scripts/check/check-ui-slim-closure.shs` | push-ui-slim-closure (push), push-ui-slim-closure-tui-entry (push) | rust-bootstrap-multiplatform.yml, code-idiom-gates.yml |
| push-ui-slim-pack-inventory | `scripts/check/check-ui-slim-pack-inventory.shs` | — | — |
| push-c-runtime-compiles | `scripts/check/check-c-runtime-compiles-push.shs` | c-runtime-compiles (bootstrap) | code-idiom-gates.yml |
| push-no-direct-rt | `scripts/check/check-no-direct-rt.shs` | no-direct-rt (bootstrap) | — |
| push-orphan-part-files | `scripts/check/check-orphan-part-files.shs` | — | — |
| push-port-io-single-owner | `scripts/check/check-port-io-single-owner.shs` | — | — |
| push-guard-wiring | `scripts/check/check-guard-wiring.shs` | guard-wiring (bootstrap), ci-guard-wiring (ci) | code-idiom-gates.yml |
| push-sosix-capsule-boundaries | `scripts/check/check-sosix-capsule-boundaries.shs` | — | — |
| push-perf-regression-tests | `scripts/check/check-perf-regression-tests.shs` | perf-regression-tests (bootstrap) | — |
| push-entry-closure-ratchet | `scripts/check/check-entry-closure-ratchet.shs` | — | — |
| push-process-wait-eintr-retry | `scripts/check/check-process-wait-eintr-retry.shs` | process-wait-eintr-retry (bootstrap) | — |
| push-mir-transient-scope-boundary | `scripts/check/check-mir-transient-scope-boundary.shs` | — | — |
| push-transient-scope-reclaims | `scripts/check/check-transient-scope-reclaims.shs` | — | — |
| push-rt-hash-text-cross-lane | `scripts/check/check-rt-hash-text-cross-lane.shs` | — | — |
| push-simd-kernels-vectorized | `scripts/check/check-simd-kernels-vectorized.shs` | — | — |
| push-vulkan-compute-real | `scripts/check/check-vulkan-compute-real.shs` | — | — |
| push-sdn-crc32-sealed | `scripts/check/check-sdn-crc32-sealed.shs` | local-sdn-crc32-sealed (local) | code-idiom-gates.yml |
| push-rust-duplicate-reexport | `scripts/check/check-rust-duplicate-reexport.shs` | local-rust-duplicate-reexport (local) | code-idiom-gates.yml |
| push-no-stale-snapshot-rewind | `scripts/check/check-no-stale-snapshot-rewind.shs` | local-no-stale-snapshot-rewind (local) | code-idiom-gates.yml |
| push-range-shs-hygiene | `scripts/check/check-range-shs-hygiene-push.shs` | local-range-shs-hygiene (local) | — |
| push-no-document-symlinks | `scripts/check/check-no-document-symlinks-push.shs` | — | — |
| push-merge-content-conservation | `scripts/check/check-merge-content-conservation-push.shs` | — | — |
| push-rules-quick | `scripts/check/check-rules-sdl.shs` | rules-full (bootstrap) | — |
| push-interpreter-module-owners | `scripts/check/check-interpreter-module-owners.shs` | interpreter-module-owners-selftest (bootstrap) | — |
| push-interpreter-extern-registry-gap | `scripts/check/check-interpreter-extern-registry-gap.shs` | interpreter-extern-registry-gap-selftest (bootstrap) | — |
| push-sffi-v2-authority | `scripts/check/check-sffi-v2-authority.shs` | — | — |
| push-type-walk-constructor-parity | `scripts/check/check-type-walk-constructor-parity.shs` | type-walk-constructor-parity-selftest (bootstrap) | — |
| push-shs-path-conversion-equivalence | `scripts/check/check-shs-path-conversion-equivalence.shs` | — | — |
| push-shs-native-tool-boundary-preserved | `scripts/check/check-shs-native-tool-boundary-preserved.shs` | — | — |
| push-windows-checkout-damage | `scripts/check/check-windows-checkout-damage-push.shs` | — | — |
| push-main-test-runnable | `scripts/check/check-main-test-runnable-push.shs` | — | — |
| push-rt-dual-implementation | `scripts/check/check-rt-dual-implementation-ratchet.shs` | local-rt-dual-implementation (local) | code-idiom-gates.yml |
| push-dual-run-shadow | `scripts/check/check-dual-run-shadow.shs` | — | — |
| push-rust-llvm23-binding | `scripts/check/check-rust-llvm23-binding.shs` | — | — |
| push-windows-directx-d3d11-lifecycle | `scripts/check/check-windows-directx-d3d11-lifecycle.shs` | — | directx-d3d11-lifecycle.yml |
| push-stage3-hir-retained-parser-rss | `scripts/check/check-stage3-hir-retained-parser-rss.shs` | — | repo-hygiene.yml |
| push-freebsd-phase2-test-runner-contract | `scripts/check/check-freebsd-phase2-test-runner-contract.shs` | — | freebsd-build.yml |
| push-linux-phase2-test-runner-contract | `scripts/check/check-linux-phase2-test-runner-contract.shs` | local-linux-phase2-test-runner-contract (local) | rust-bootstrap-multiplatform.yml |
| push-windows-msvc-toolchain-contract | `scripts/check/check-windows-msvc-toolchain-contract.shs` | — | — |
| push-tracking-doc-registration | `scripts/check/check-tracking-doc-registration.shs` | — | — |
| push-nested-fn-jit-lowering | `scripts/check/check-nested-fn-jit-lowering.shs` | — | — |
| push-bootstrap-lane-verdict-line | `scripts/check/check-bootstrap-lane-verdict-line.shs` | — | — |
| push-runner-binary-extern-freshness | `scripts/check/check-runner-binary-extern-freshness.shs` | — | — |
| push-parser-source-global-ratchet | `scripts/check/check-parser-source-global-ratchet.shs` | — | — |
| push-rt-api-groups | `scripts/check/check-rt-api-groups.shs` | — | — |
| push-runtime-source-list-parity | `scripts/check/check-runtime-source-list-parity.shs` | — | — |
| push-no-mock-file-system-io | `scripts/check/check-no-mock-file-system-io.shs` | — | — |
| push-transient-scope-text-field-promotion | `scripts/check/check-transient-scope-text-field-promotion.shs` | — | — |
| push-lifecycle-reachability | `scripts/check/check-lifecycle-reachability.shs` | — | code-idiom-gates.yml |
| push-no-unwind-lib-dependency | `scripts/check/check-no-unwind-lib-dependency.shs` | — | — |
| push-native-text-abi-and-binary-read | `scripts/check/check-native-text-abi-and-binary-read.shs` | — | — |
| push-aot-failure-speaks | `scripts/check/check-aot-failure-speaks.shs` | — | — |
| push-runtime-shared-library | `scripts/check/check-runtime-shared-library.shs` | — | — |
| push-native-text-to-i64-parses | `scripts/check/check-native-text-to-i64-parses.shs` | — | — |
| push-scv-inventory-resource-profile | `scripts/check/check-scv-inventory-resource-profile.shs` | — | — |
| push-stage4-dynamic-runtime-lane | `scripts/check/check-stage4-dynamic-runtime-lane.shs` | — | — |
| push-llm-caret-server-serves | `scripts/check/check-llm-caret-server-serves.shs` | — | — |
| push-plan-acceptance-swept | `scripts/check/check-plan-acceptance-swept.shs` | plan-acceptance-swept (bootstrap) | — |
| push-local-ci-receipt-selftest | `scripts/check/verify-local-ci-receipt.shs` | — | code-idiom-receipt.yml |
| push-cross-unit-user-to-text-not-hijacked | `scripts/check/check-cross-unit-user-to-text-not-hijacked.shs` | — | — |
| push-base64url-codegen-lane-perf | `scripts/check/check-base64url-codegen-lane-perf.shs` | — | — |
| push-native-build-entry-memory-budget | `scripts/check/check-native-build-entry-memory-budget.shs` | — | — |
| push-tracking-db-unique-ids | `scripts/check/check-tracking-db-unique-ids.shs` | — | — |
| push-frontend-closure-memory-budget | `scripts/check/check-frontend-closure-memory-budget.shs` | — | — |
| push-rect-batch-spirv-pinned | `scripts/check/check-rect-batch-spirv-pinned.shs` | — | — |
| push-blit-spirv-pinned | `scripts/check/check-blit-spirv-pinned.shs` | — | — |
| push-blur-rect-spirv-pinned | `scripts/check/check-blur-rect-spirv-pinned.shs` | — | — |
| push-shadow-rect-spirv-pinned | `scripts/check/check-shadow-rect-spirv-pinned.shs` | — | — |
| push-glass-material-spirv-pinned | `scripts/check/check-glass-material-spirv-pinned.shs` | — | — |
| push-chrome-dynlib-probe | `scripts/check/check-chrome-dynlib-probe.shs` | — | — |
| push-font-catalog-pointer-release-perf | `scripts/check/check-font-catalog-pointer-release-perf.shs` | — | — |
| push-simpleos-x86-kernel-elf-fixture | `scripts/check/check-simpleos-x86-kernel-elf-fixture.shs` | — | — |
| push-cache-writer-runtime-provisioning | `scripts/check/check-cache-writer-runtime-provisioning.shs` | — | — |
| push-simpleos-ssp-linkage | `scripts/check/check-simpleos-ssp-linkage.shs` | — | — |
| push-simpleos-harden-probe-build-target | `scripts/check/check-simpleos-harden-probe-build-target.shs` | — | — |
| push-allocation-registry-churn | `scripts/check/check-allocation-registry-churn.shs` | — | — |
| push-windows-coff-compat-alias-gc | `scripts/check/check-windows-coff-compat-alias-gc.shs` | — | — |
| push-kernel-closure | `scripts/check/check-kernel-closure.shs` | — | repo-hygiene.yml |

Summary: no_visible_mapping=56, other_registry_row=19, total=81, workflow_mention=16.

A destination is accepted only after inspecting the called workflow/job and its required-status policy. This inventory is for that audit; it does not change gate enforcement.
