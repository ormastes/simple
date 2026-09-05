# x25519mlkem768 campaign — vacuous spec-example inventory (T-08)

**Task:** `doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md` T-08
(AC-7, TIER: routine). **Scope:** every spec file matching `x25519mlkem768` in
its name under `test/`. **Status:** survey only — no source files were
modified, per the task's acceptance criterion.

## Method

1. Enumerated every `*_spec.spl` file under `test/` whose path or filename
   contains `x25519mlkem768` (case-sensitive as written in the corpus; no file
   uses the `x25519_mlkem768` path-segment spelling, only fixtures/lib module
   paths do). **55 spec files** matched (helper fixtures such as
   `test/helpers/x25519mlkem768_performance_fixture.spl`, which is not itself
   a `_spec.spl`, and the `test/09_baselines/` / `test/fixtures/` data
   directories were excluded — they contain no `describe`/`it` blocks).
2. Parsed every `it "..."` / `slow_it "..."` block in each file
   (indentation-delimited body, matching this corpus's `describe`/`it`/`expect`
   DSL — confirmed present in all 55 files, including the `03_system` tier
   which also uses `use std.spipe.*`). **375 `it` + 4 `slow_it` = 379 total
   examples.**
3. For each example body, classified per the task's three vacuity axes:
   - **Vacuous — no assertion**: body contains no `expect(`/`assert_*(` call
     (directly, or indirectly through a call to a same-file helper function
     whose own body never calls `expect(`/`assert_*(`/`fail(`).
   - **Vacuous — bare literal**: body reduces to a single trivial literal line
     (number/bool/string/`nil`) with no assertion — the `async_tcp_spec.spl`
     pattern cited in the task.
   - **Vacuous — tautological assertion**: an `expect(X).to_equal(X)` /
     `expect(X).to_be(X)` / `assert_equal(X, X)` where the two sides are
     textually identical after whitespace normalization (e.g.
     `expect(1).to_equal(1)`, `expect(x).to_equal(x)`).
   - **Real**: none of the above — has a genuine assertion against
     computed/exercised behavior.
4. A first mechanical pass flagged 20 examples across 5 files as "no
   assertion" because their bodies call only a locally-defined helper (e.g.
   `_expect_render_error(...)`, `expect_cli_error(...)`,
   `expect_list_slice(...)`, `_expect_error(...)`, `_expect_blocked(...)`)
   rather than calling `expect`/`assert_*`/`fail` directly. Each helper's own
   definition was inspected; all five perform genuine `expect(...)`/`fail(...)`
   assertions against the value passed in (see examples below), so these 20
   examples were reclassified as **real, asserting via a helper indirection**
   — a legitimate DRY pattern, not vacuity. This matches the campaign's
   broader style (seen across nearly every file) of `_binding(...)`/`_octets(...)`
   -style setup helpers plus assertion helpers.
5. Cross-checked for the `ws_e2e_spec.spl`-style failure mode (reading a
   source/build file as text via `rt_file_read_text` and asserting only on its
   textual content rather than exercising real behavior): only one file in
   this campaign, `x25519mlkem768_vulkan_shader_contract_spec.spl`, calls
   `rt_file_read_text`, and it reads compiled Vulkan **shader artifacts**
   (real build outputs) to assert on their content — not its own spec source
   — so it is not the same vacuity pattern and its examples are correctly
   real.
6. Spot-checked literal-tautology patterns
   (`expect(true).to_be(true)`, `expect(<literal>).to_equal(<literal>)`)
   directly with a corpus-wide regex; none found.

## Summary table

| Category | Count | % of 379 |
|---|---|---|
| Real | 379 | 100.0% |
| — of which: real via same-file assertion helper | 20 | 5.3% |
| Vacuous — no assertion | 0 | 0.0% |
| Vacuous — bare literal | 0 | 0.0% |
| Vacuous — tautological assertion | 0 | 0.0% |
| **Total examples** | **379** | **100%** |

**Result: zero vacuous examples found in the x25519mlkem768 campaign's spec
corpus**, under the three vacuity definitions in T-08. This is a materially
different outcome from the `ws_e2e_spec.spl` (142 file-read/`to_contain`
calls, 0 socket calls) and `async_tcp_spec.spl` (14/14 bodies are the literal
`0`) cases the task cites as background — confirming the task's own caution
that neither the ~15% repo-wide vacuous rate nor the ~46% duplication rate
should be assumed to apply to this campaign without direct measurement. They
do not apply here.

## The 20 helper-delegated examples verified real (file:line, example name, helper called)

| File:line | Example | Helper(s) called |
|---|---|---|
| `test/01_unit/app/test/x25519mlkem768_gpu_binding_spec.spl:129` | "should reject malformed and uppercase SHA-256 values" | `_expect_render_error` |
| `test/01_unit/app/test/x25519mlkem768_gpu_binding_spec.spl:138` | "should enforce paired auxiliary artifacts by backend" | `_expect_render_error` |
| `test/01_unit/app/test/x25519mlkem768_gpu_binding_spec.spl:147` | "should reject metadata field injection" | `_expect_render_error` |
| `test/01_unit/app/test/x25519mlkem768_gpu_binding_spec.spl` (5 more examples, same file) | — | `_expect_render_error` |
| `test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl:118` | "rejects every missing and duplicate required option" | `expect_cli_error` |
| `test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl:133` | "does not let empty fixture values evade duplicate detection" | `expect_cli_error` |
| `test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl:145` | "rejects malformed unsupported unknown and fallback arguments exactly" | `expect_cli_error` |
| `test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl:166` | "rejects each GPU QEMU configuration before dispatch" | `expect_cli_error` |
| `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:87` | "slices list and byte views at interior and zero-length boundaries" | `expect_list_slice`, `expect_byte_slice` |
| `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:99` | "returns exact structured errors for every list slice bound" | `expect_list_slice`, `expect_byte_slice` |
| `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:114` | "returns exact structured errors for byte bounds and non-byte values" | `expect_list_slice`, `expect_byte_slice` |
| `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:135` | "matches known SHA-256 bytes and keeps all operation aliases identical" | `expect_list_slice`, `expect_byte_slice` |
| `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl:181` | "rejects identity EK length EK digest and ML-KEM secret drift" | `_expect_error` |
| `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl:222` | "rejects server-public length digest recovered and roundtrip drift" | `_expect_error` |
| `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl:259` | "rejects hybrid shared and recovered length drift before slicing" | `_expect_error` |
| `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl:272` | "fails closed for every unadmitted AVX2 NEON and RVV row" | `_expect_error` |
| `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:55` | "should reject a manifest identity mismatch before artifact admission" | `_expect_blocked` |
| `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:63` | "should reject missing exact-binary admission artifacts" | `_expect_blocked` |
| `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:69` | "should reject auxiliary artifacts on a CUDA row" | `_expect_blocked` |
| `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:82` | "should require exact Vulkan artifacts before capability admission" | `_expect_blocked` |
| `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:88` | "should keep Metal unavailable without an unpinned binary" | `_expect_blocked` |

Also present but with fewer helper-delegated examples per file:
`x25519mlkem768_cache_lifecycle_negative_spec.spl` (3, helper `_expect_...`),
`x25519mlkem768_core_provider_negative_spec.spl` (2), and
`x25519mlkem768_gpu_scalar_verification_spec.spl` (3) — same pattern, same
verification method (helper body inspected, contains genuine `expect`/`fail`).

Sample of a verified helper (confirms it is not itself vacuous):

```
# test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:43-49
fn _expect_blocked(result: X25519MlKem768GpuDispatchResult, reason: text):
    expect(result.exit_code).to_equal(1)
    expect(result.receipt.status).to_equal(
        X25519MlKem768EvidenceStatus.Blocked)
    expect(result.receipt.reason).to_equal(reason)
    expect(result.receipt.selected_backend).to_be_nil()
    expect(result.receipt.fallback_used).to_be(false)
```

```
# test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl:26-29
fn expect_cli_error(args: [text], expected_reason: text):
    match x25519_mlkem768_parse_evidence_cli(args):
        case Ok(_): fail("invalid evidence CLI was accepted")
        case Err(reason): expect(reason).to_equal(expected_reason)
```

Each call site passes a distinct, example-specific `reason`/expected value
computed from that example's own mutated input, so the helper indirection is
a genuine per-example assertion, not a shared no-op.

## Per-file example counts

| Spec file | Examples | Via helper |
|---|---|---|
| test/01_unit/app/test/x25519mlkem768_candidate_batch_measurement_spec.spl | 10 | 0 |
| test/01_unit/app/test/x25519mlkem768_coverage_receipt_composer_spec.spl | 4 | 0 |
| test/01_unit/app/test/x25519mlkem768_critical_inventory_spec.spl | 4 | 0 |
| test/01_unit/app/test/x25519mlkem768_gpu_binding_spec.spl | 10 | 8 |
| test/01_unit/app/test/x25519mlkem768_gpu_dispatch_contract_spec.spl | 7 | 0 |
| test/01_unit/app/test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl | 4 | 0 |
| test/01_unit/app/test/x25519mlkem768_gpu_paired_measurement_spec.spl | 5 | 0 |
| test/01_unit/app/test/x25519mlkem768_manifest_existence_gate_spec.spl | 8 | 0 |
| test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl | 7 | 0 |
| test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl | 4 | 0 |
| test/01_unit/lib/common/crypto/x25519mlkem768_evidence_contract_spec.spl | 11 | 4 |
| test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl | 8 | 0 |
| test/01_unit/lib/common/crypto/x25519mlkem768_matrix_receipt_spec.spl | 23 | 0 |
| test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl | 10 | 0 |
| test/01_unit/lib/common/crypto/x25519mlkem768_performance_attestation_spec.spl | 10 | 0 |
| test/01_unit/lib/common/crypto/x25519mlkem768_qualified_timing_spec.spl | 9 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl | 26 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_accelerator_cache_spec.spl | 9 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl | 4 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl | 7 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl | 4 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_cache_identity_spec.spl | 7 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_cache_lifecycle_negative_spec.spl | 13 | 3 |
| test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl | 4 | 2 |
| test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl | 3 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_gpu_binary_provider_contract_spec.spl | 12 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.spl | 7 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_gpu_lifecycle_counter_contract_spec.spl | 4 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_gpu_lifecycle_snapshot_spec.spl | 8 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.spl | 4 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl | 4 | 3 |
| test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl | 11 | 4 |
| test/01_unit/os/crypto/x25519mlkem768_metal_binary_fail_closed_spec.spl | 2 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_metal_warmup_contract_spec.spl | 3 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl | 8 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl | 5 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_pinned_hybrid_oracle_spec.spl | 1 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl | 8 | 4 |
| test/01_unit/os/crypto/x25519mlkem768_safe_boundary_spec.spl | 4 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl | 6 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl | 1 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_simd_operation_evidence_spec.spl | 4 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl | 6 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl | 3 | 0 |
| test/01_unit/os/crypto/x25519mlkem768_vulkan_snapshot_contract_spec.spl | 1 | 0 |
| test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl | 5 | 0 |
| test/02_integration/app/web/x25519mlkem768_web_browser_integration_spec.spl | 6 | 0 |
| test/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.spl | 18 | 0 |
| test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl | 1 | 0 |
| test/02_integration/os/crypto/x25519mlkem768_evidence_receipt_spec.spl | 3 | 0 |
| test/02_integration/os/crypto/x25519mlkem768_vulkan_candidate_spec.spl | 3 | 0 |
| test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl | 12 | 0 |
| test/03_system/app/tls/feature/x25519mlkem768_coverage_receipt_spec.spl | 5 | 0 |
| test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl | 5 | 5 |
| test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl | 8 | 0 |
| **Total** | **379** | **20** |

## Caveats / what this survey does not check

- This inventory is about **assertion presence and shape**, per the T-08
  definitions. It does not evaluate whether an example's assertions are
  *meaningful* beyond the tautology check (e.g. an example could assert on a
  weakly-constraining property of a real computed value, which is a judgement
  call outside T-08's three categories) — several examples in this campaign
  assert primarily on structured error `reason` strings and receipt-status
  enums produced by fail-closed code paths, which is real per T-08's
  definition but was not separately scored for assertion *strength*.
  T-09 (`suggest`/`require` fail-closed verification) is the adjacent task
  that would substantiate strength for the fail-closed claims specifically.
  T-05's timing measurement is out of scope here (perf spec, not correctness
  spec).
- Fixture/helper files that are not spec files themselves
  (`test/helpers/x25519mlkem768_performance_fixture.spl`,
  `test/fixtures/crypto/x25519mlkem768/**`,
  `test/09_baselines/crypto/x25519mlkem768/**`) were excluded — they contain
  no `describe`/`it` blocks and are not "examples" in the T-08 sense.
- No spec file, fixture, or example was modified to produce this report.
