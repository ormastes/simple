# X25519mlkem768 Security Contract Specification

> Tests covering X25519MLKEM768 security source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Security Contract Specification

## Scenarios

### X25519MLKEM768 security source contract

#### should use full-scan equality and arithmetic FO selection (NFR-004)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should use full-scan equality and arithmetic FO selection (NFR-004)
- Inspect constant-work equality and FO selection sources
   - Expected: source does not contain `if c == c_prime`
   - Expected: source does not contain `if c != c_prime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should use full-scan equality and arithmetic FO selection (NFR-004)")
step("Inspect constant-work equality and FO selection sources")
val source = file_read_text("src/os/crypto/ml_kem.spl")
expect(source).to_contain("fn _ct_bytes_eq(a: list, b: list) -> i64:")
expect(source).to_contain("acc = acc & _ct_byte_eq(a.get(i), b.get(i))")
expect(source).to_contain("val selected = _ct_select_bytes(mask, k_prime, k_implicit)")
expect(source.contains("if c == c_prime")).to_equal(false)
expect(source.contains("if c != c_prime")).to_equal(false)
```

</details>

#### should keep the production X25519 backend free of diagnostics and merge artifacts (REQ-016)

- should keep the production X25519 backend free of diagnostics and merge artifacts (REQ-016)
- Scan the production X25519 backend for diagnostics and conflict markers
   - Expected: source does not contain `serial_println`
   - Expected: source does not contain `<<<<<<<`
   - Expected: source does not contain `>>>>>>>`
   - Expected: source does not contain `%%%%%%%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should keep the production X25519 backend free of diagnostics and merge artifacts (REQ-016)")
step("Scan the production X25519 backend for diagnostics and conflict markers")
val source = file_read_text("src/os/crypto/curve25519_smalllimb.spl")
expect(source.contains("serial_println")).to_equal(false)
expect(source.contains("<<<<<<<")).to_equal(false)
expect(source.contains(">>>>>>>")).to_equal(false)
expect(source.contains("%%%%%%%")).to_equal(false)
```

</details>

#### should perform a full all-zero aggregation before rejection (NFR-004)

- should perform a full all-zero aggregation before rejection (NFR-004)
- Exercise zero and nonzero values at every scan boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should perform a full all-zero aggregation before rejection (NFR-004)")
step("Exercise zero and nonzero values at every scan boundary")
var bytes: [u8] = [0.to_u8(), 0.to_u8(), 0.to_u8()]
expect(x25519_mlkem768_bytes_all_zero(bytes)).to_be(true)
bytes[0] = 1.to_u8()
expect(x25519_mlkem768_bytes_all_zero(bytes)).to_be(false)
bytes[0] = 0.to_u8()
bytes[1] = 1.to_u8()
expect(x25519_mlkem768_bytes_all_zero(bytes)).to_be(false)
bytes[1] = 0.to_u8()
bytes[2] = 1.to_u8()
expect(x25519_mlkem768_bytes_all_zero(bytes)).to_be(false)
```

</details>

#### should route production TLS entropy only through the canonical facade (NFR-006)

- should route production TLS entropy only through the canonical facade (NFR-006)
- Inspect TLS imports and the exact-fill platform boundary
   - Expected: client does not contain `random_bytes(`
   - Expected: server does not contain `random_bytes(`
   - Expected: entropy does not contain `use os.crypto.random`
   - Expected: entropy does not contain `entropy_platform_ready`
   - Expected: entropy does not contain `_entropy_all_zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should route production TLS entropy only through the canonical facade (NFR-006)")
step("Inspect TLS imports and the exact-fill platform boundary")
val client = file_read_text("src/os/tls13/_Tls13/handshake.spl")
val server = file_read_text("src/os/tls13/server.spl")
val entropy = file_read_text("src/os/crypto/entropy.spl")
val platform = file_read_text(
    "src/lib/nogc_sync_mut/crypto/entropy_platform.spl")
val runtime = file_read_text("src/runtime/runtime_native.c")
val aggregate_lowering = file_read_text(
    "src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl")
expect(client).to_contain(
    r"use os.crypto.entropy.{crypto_entropy_bytes}")
expect(server).to_contain(
    r"use os.crypto.entropy.{crypto_entropy_bytes}")
expect(client.contains("random_bytes(")).to_equal(false)
expect(server.contains("random_bytes(")).to_equal(false)
expect(entropy.contains("use os.crypto.random")).to_equal(false)
expect(entropy.contains("entropy_platform_ready")).to_equal(false)
expect(entropy.contains("_entropy_all_zero")).to_equal(false)
expect(entropy).to_contain("match entropy_platform_bytes(count):")
expect(entropy).to_contain("crypto_entropy_validate_candidate_for_test")
expect(platform).to_contain("extern fn rt_entropy_fill(bytes: [u8]) -> i64")
expect(platform).to_contain("var bytes: [u8] = []")
expect(platform).to_contain("if rt_entropy_fill(bytes) != 1:")
expect(platform).to_contain("_entropy_platform_wipe(bytes)")
expect(aggregate_lowering).to_contain(
    r"call ptr @rt_array_new(i64 {operands.len()})")
expect(runtime).to_contain(
    "return (int64_t)getrandom(destination, length, 0)")
expect(runtime).to_contain("getentropy(destination, length)")
expect(runtime).to_contain("BCRYPT_USE_SYSTEM_PREFERRED_RNG")
expect(runtime).to_contain("SIMPLE_RUNTIME_ENTROPY_TESTING")
expect(runtime).to_contain("rt_entropy_provider_read(")
expect(runtime).to_contain("rt_entropy_zero_array(array)")
expect(runtime).to_contain("array->flags != 0 &&")
expect(runtime).to_contain(
    "array->flags != RT_CORE_ARRAY_FLAG_BYTES")
expect(runtime).to_contain(
    "slots[i] = rt_value_int((int64_t)temporary[i])")
val readiness = runtime.index_of(
    "int64_t rt_entropy_hardware_ready(void)")
val readiness_failure = runtime.index_of("return 0;", readiness)
expect(readiness).to_be_greater_than(-1)
expect(readiness_failure).to_be_greater_than(readiness)
```

</details>

#### should keep every GPU implementation candidate-only outside production TLS (NFR-007)

- should keep every GPU implementation candidate-only outside production TLS (NFR-007)
- Inspect production TLS modules for specialized backend references
   - Expected: client does not contain `_cuda_candidate`
   - Expected: client does not contain `_metal_candidate`
   - Expected: client does not contain `_vulkan_candidate`
   - Expected: server does not contain `_cuda_candidate`
   - Expected: server does not contain `_metal_candidate`
   - Expected: server does not contain `_vulkan_candidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should keep every GPU implementation candidate-only outside production TLS (NFR-007)")
step("Inspect production TLS modules for specialized backend references")
val policy = file_read_text(
    "src/os/crypto/x25519_mlkem768/execution_policy.spl")
val client = file_read_text("src/os/tls13/_Tls13/handshake.spl")
val server = file_read_text("src/os/tls13/server.spl")
expect(policy).to_contain("automatic:scalar-cpu")
expect(policy).to_contain("candidate-only: not production-promoted")
expect(client.contains("_cuda_candidate")).to_equal(false)
expect(client.contains("_metal_candidate")).to_equal(false)
expect(client.contains("_vulkan_candidate")).to_equal(false)
expect(server.contains("_cuda_candidate")).to_equal(false)
expect(server.contains("_metal_candidate")).to_equal(false)
expect(server.contains("_vulkan_candidate")).to_equal(false)
```

</details>

#### should emit only public-share and artifact digests (NFR-004 NFR-007)

- should emit only public-share and artifact digests (NFR-004 NFR-007)
- Inspect evidence construction for secret-bearing fields
   - Expected: hybrid does not contain `_hybrid_digest(shared)`
   - Expected: hybrid does not contain `_hybrid_digest(mlkem_shared)`
   - Expected: hybrid does not contain `_hybrid_digest(x25519_shared)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should emit only public-share and artifact digests (NFR-004 NFR-007)")
step("Inspect evidence construction for secret-bearing fields")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(hybrid).to_contain(
    "Evidence hashes only the public server share; never a shared secret.")
expect(hybrid.contains("_hybrid_digest(shared)")).to_equal(false)
expect(hybrid.contains("_hybrid_digest(mlkem_shared)")).to_equal(false)
expect(hybrid.contains("_hybrid_digest(x25519_shared)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 security source contract.
- X25519MLKEM768 security source contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `54c8235801328e639cf621937679249e0db3e46f83cfa2cd94e60370aaf35a7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54c8235801328e639cf621937679249e0db3e46f83cfa2cd94e60370aaf35a7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54c8235801328e639cf621937679249e0db3e46f83cfa2cd94e60370aaf35a7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_security_contract_spec.md (current)
findings: 13 blockers: 2
  narrative=100 structure=70 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/01_unit/os/crypto/x25519mlkem768_security_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_security_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use full-scan equality and arithmetic FO selection (NFR-004)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use full-scan equality and arithmetic FO selection (NFR-004)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the production X25519 backend free of diagnostics and merge artifacts (REQ-016)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the production X25519 backend free of diagnostics and merge artifacts (REQ-016)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should perform a full all-zero aggregation before rejection (NFR-004)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should perform a full all-zero aggregation before rejection (NFR-004)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route production TLS entropy only through the canonical facade (NFR-006)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep every GPU implementation candidate-only outside production TLS (NFR-007)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_security_contract_spec.spl:120:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit only public-share and artifact digests (NFR-004 NFR-007)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
