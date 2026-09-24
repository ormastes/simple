# Cross-renderer performance comparison admission

This artifact-only SPipe manual describes the shared admission gate for the C
Vulkan/Simple and Chrome/Simple Web comparisons. It never launches Vulkan,
Chrome, or a renderer. A green contract check proves only that malformed or
incomplete evidence is refused; it is not a rendering or performance result.

| Field | Value |
|-------|-------|
| Requirements | REQ-GPUUI-007, NFR-GPUUI-002, NFR-GPUUI-003 |
| Source | `test/03_system/check/perf_comparison_admission_contract_spec.spl` |
| Gate | `scripts/check/lib/perf-comparison-admission.shs` |
| Evidence class | artifact-only admission |
| Runtime status | pending an admitted pure-Simple worker |

## Admission contract

Both rows must use the same workload and event script, viewport, timing
boundary, readback/capture mode, warmup count, sample count, GPU identity,
fallback state, checksum semantics, and checksum. Each side independently
binds its source, executable, admission receipt, and output artifact to their
current hashes. Source revisions may differ because C, Simple, and Chrome are
different implementations.

The gate rejects software, unknown, synthetic, unverified, and fallback GPU
identity/state before a ratio is calculated. It also rejects missing,
duplicate, injected, stale, or malformed fields and forbidden seed binaries.

## Scenarios

The manual mirrors the 11 executable cases and their asserted verdicts. Each
case also requires process exit code `0`; a skipped admission is a deliberate
fail-closed data verdict rather than a shell failure.

| Executable scenario | Manual step | Required output |
|---------------------|-------------|-----------------|
| `should admit distinct implementations when each source revision is currently pinned` | Create independently source-bound admission-fixture rows | `status=admitted`; `reason=admitted` |
| `should reject duplicate keys instead of using the last value` | Append a forged second workload identity | `status=skipped`; `duplicate-key-workload_id` |
| `should reject unknown injected rows` | Append a newline-shaped injected field | `unexpected-key-compare_status` |
| `should skip a GPU identity mismatch before ratio calculation` | Change only the right contract-test device identity | `reason=mismatch-gpu_identity` |
| `should reject software fallback even when both rows agree` | Mark both sides as software fallback | `reason=fallback-software` |
| `should reject unknown GPU identity even when fallback state is none` | Replace both contract-test device identities with `unknown` | `reason=invalid-gpu-identity` |
| `should reject a viewport mismatch before calculating a ratio` | Change only the right viewport width | `reason=mismatch-viewport_width` |
| `should reject a non-comparable checksum before calculating a ratio` | Inject punctuation outside the checksum schema | `reason=invalid-checksum` |
| `should reject stale artifact replay` | Mutate the measured artifact after its row was sealed | `reason=stale-left-artifact` |
| `should reject a seed path even when its hash and receipt are internally consistent` | Rebind the left row to a copied executable under a forbidden seed path | `reason=seed-left-binary-forbidden` |
| `should report missing canonical Simple artifacts without a ratio` | Provide no complete canonical comparison bundle | `chrome_simple_web_status=skipped`; `chrome_simple_web_reason=missing-canonical-artifact`; `chrome_simple_web_ratio_x1000=0` |

## Evidence interpretation

The fixture contains viewport dimensions, warmup and sample counts, timing
scope, GPU identity, fallback state, and checksum metadata. Its
`contract-test-gpu` identity is an explicit schema fixture label, not device
evidence. The fixture does not provide physical-device receipts, p50/p95
timings, RSS, or a checksum from a real renderer. Those values must come from
the admitted C Vulkan, Simple Vulkan, Simple Web, and Chrome workers using the
same fixture before any ratio can be reported. Software fallback or unknown
identity remains `skipped`, never `PASS`.

## Execution

The source spec is intended for the compiled SPipe runner. In this worktree no
admitted pure-Simple worker is available, so execution was not retried and no
runtime result is claimed. The source and mirror must remain synchronized when
the worker is restored.
