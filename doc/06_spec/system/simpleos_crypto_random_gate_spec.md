# Simpleos Crypto Random Gate Specification

> Tests covering SimpleOS crypto random production gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Crypto Random Gate Specification

## Scenarios

### SimpleOS crypto random production gate

#### keeps public random_bytes on the CSPRNG path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps public random_bytes on the CSPRNG path


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps public random_bytes on the CSPRNG path")
val source = rt_file_read_text("src/os/crypto/random.spl")

assert_contains(source, "fn random_bytes(count: u64) -> [u8]")
assert_contains(source, "if not g_csprng.initialized:")
assert_contains(source, "_csprng_init()")
assert_equal(source.contains("_soft_random_u64"), false)
assert_equal(source.contains("return host_bytes"), false)
```

</details>

#### selects platform entropy hooks instead of hardcoding x86

- selects platform entropy hooks instead of hardcoding x86


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects platform entropy hooks instead of hardcoding x86")
val source = rt_file_read_text("src/os/crypto/random.spl")

assert_contains(source, "@cfg(x86_64)")
assert_contains(source, "rt_rdrand()")
assert_contains(source, "@cfg(arm64)")
assert_contains(source, "rt_rndr()")
assert_contains(source, "@cfg(riscv64)")
assert_contains(source, "rt_riscv_seed()")
```

</details>

#### documents that shimmed entropy is not production entropy

- documents that shimmed entropy is not production entropy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents that shimmed entropy is not production entropy")
val source = rt_file_read_text("src/os/crypto/random.spl")
val shim = rt_file_read_text("src/os/kernel/net/tls_shim.spl")

assert_contains(source, "not a production entropy source")
assert_contains(shim, "NOT cryptographically secure")
```

</details>

#### uses RISC-V CSR jitter instead of the LCG for rt_riscv_seed

- uses RISC-V CSR jitter instead of the LCG for rt_riscv_seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses RISC-V CSR jitter instead of the LCG for rt_riscv_seed")
val shim = rt_file_read_text("src/os/kernel/net/tls_shim.spl")
val entropy = rt_file_read_text("src/os/kernel/arch/riscv64/entropy.spl")

assert_contains(shim, "fn rt_riscv_seed() -> u64")
assert_contains(shim, "csrr_cycle()")
assert_contains(shim, "csrr_time()")
assert_contains(shim, "csrr_instret()")
assert_contains(entropy, "fn entropy_seed_u64() -> u64")
assert_contains(entropy, "csrr_cycle() ^")
assert_contains(entropy, "csrr_time() ^")
assert_contains(entropy, "csrr_instret() ^")
```

</details>

#### keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path

- keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path")
val runtime = rt_file_read_text("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")
val shim = rt_file_read_text("src/os/kernel/net/tls_shim.spl")

assert_contains(runtime, "static int _cpu_has_rdrand(void)")
assert_contains(runtime, "cpuid")
assert_contains(runtime, "ecx & (1u << 30)")
assert_contains(runtime, "rdrand %0; setc %1")
assert_contains(runtime, "for (int attempt = 0; attempt < 10; attempt++)")
assert_contains(runtime, "int64_t rt_entropy_hardware_ready(void)")
assert_contains(runtime, "return _cpu_has_rdrand() ? 1 : 0;")
assert_contains(shim, "extern fn rt_entropy_hardware_ready() -> i64")
assert_contains(shim, "rt_entropy_hardware_ready() > 0")
assert_equal(runtime.contains("rt_rdrand: pseudo-random"), false)
```

</details>

#### keeps RISC-V TLS entropy explicitly not-ready until hardware RNG exists

- keeps RISC-V TLS entropy explicitly not-ready until hardware RNG exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps RISC-V TLS entropy explicitly not-ready until hardware RNG exists")
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")

assert_contains(runtime, "spl_i64 rt_entropy_hardware_ready(void)")
assert_contains(runtime, "return 0;")
assert_equal(runtime.contains("sbi_get_random"), false)
assert_equal(runtime.contains("csrr_seed"), false)
assert_equal(runtime.contains("rt_rdrand"), false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/system/simpleos_crypto_random_gate_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS crypto random production gate.
- SimpleOS crypto random production gate

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9da66b264281c9554a665a79f382bbeea5c348a5c487c78894d192e9a46f6618`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9da66b264281c9554a665a79f382bbeea5c348a5c487c78894d192e9a46f6618`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9da66b264281c9554a665a79f382bbeea5c348a5c487c78894d192e9a46f6618`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/system/simpleos_crypto_random_gate_spec.spl
mirror: doc/06_spec/system/simpleos_crypto_random_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/simpleos_crypto_random_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/simpleos_crypto_random_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/simpleos_crypto_random_gate_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/simpleos_crypto_random_gate_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps public random_bytes on the CSPRNG path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/simpleos_crypto_random_gate_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects platform entropy hooks instead of hardcoding x86' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/simpleos_crypto_random_gate_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents that shimmed entropy is not production entropy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
