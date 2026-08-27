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
   - Expected: source does not contain `_soft_random_u64`
   - Expected: source does not contain `return host_bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps public random_bytes on the CSPRNG path")
val source = rt_file_read_text("src/os/crypto/random.spl")

expect(source).to_contain("fn random_bytes(count: u64) -> [u8]")
expect(source).to_contain("if not g_csprng.initialized:")
expect(source).to_contain("_csprng_init()")
expect(source.contains("_soft_random_u64")).to_equal(false)
expect(source.contains("return host_bytes")).to_equal(false)
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

expect(source).to_contain("@cfg(x86_64)")
expect(source).to_contain("rt_rdrand()")
expect(source).to_contain("@cfg(arm64)")
expect(source).to_contain("rt_rndr()")
expect(source).to_contain("@cfg(riscv64)")
expect(source).to_contain("rt_riscv_seed()")
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

expect(source).to_contain("not a production entropy source")
expect(shim).to_contain("NOT cryptographically secure")
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

expect(shim).to_contain("fn rt_riscv_seed() -> u64")
expect(shim).to_contain("csrr_cycle()")
expect(shim).to_contain("csrr_time()")
expect(shim).to_contain("csrr_instret()")
expect(entropy).to_contain("fn entropy_seed_u64() -> u64")
expect(entropy).to_contain("csrr_cycle() ^")
expect(entropy).to_contain("csrr_time() ^")
expect(entropy).to_contain("csrr_instret() ^")
```

</details>

#### keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path

- keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path
   - Expected: runtime does not contain `rt_rdrand: pseudo-random`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path")
val runtime = rt_file_read_text("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")
val shim = rt_file_read_text("src/os/kernel/net/tls_shim.spl")

expect(runtime).to_contain("static int _cpu_has_rdrand(void)")
expect(runtime).to_contain("cpuid")
expect(runtime).to_contain("ecx & (1u << 30)")
expect(runtime).to_contain("rdrand %0; setc %1")
expect(runtime).to_contain("for (int attempt = 0; attempt < 10; attempt++)")
expect(runtime).to_contain("int64_t rt_entropy_hardware_ready(void)")
expect(runtime).to_contain("return _cpu_has_rdrand() ? 1 : 0;")
expect(shim).to_contain("extern fn rt_entropy_hardware_ready() -> i64")
expect(shim).to_contain("rt_entropy_hardware_ready() > 0")
expect(runtime.contains("rt_rdrand: pseudo-random")).to_equal(false)
```

</details>

#### keeps RISC-V TLS entropy explicitly not-ready until hardware RNG exists

- keeps RISC-V TLS entropy explicitly not-ready until hardware RNG exists
   - Expected: runtime does not contain `sbi_get_random`
   - Expected: runtime does not contain `csrr_seed`
   - Expected: runtime does not contain `rt_rdrand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps RISC-V TLS entropy explicitly not-ready until hardware RNG exists")
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")

expect(runtime).to_contain("spl_i64 rt_entropy_hardware_ready(void)")
expect(runtime).to_contain("return 0;")
expect(runtime.contains("sbi_get_random")).to_equal(false)
expect(runtime.contains("csrr_seed")).to_equal(false)
expect(runtime.contains("rt_rdrand")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_crypto_random_gate_spec.spl` |
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `74085591807ed16a333d6afe703887f8a19ba1b2908c9ca26c176216bd58ebfe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74085591807ed16a333d6afe703887f8a19ba1b2908c9ca26c176216bd58ebfe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74085591807ed16a333d6afe703887f8a19ba1b2908c9ca26c176216bd58ebfe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_crypto_random_gate_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_crypto_random_gate_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_crypto_random_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_crypto_random_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_crypto_random_gate_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/os/simpleos_crypto_random_gate_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps public random_bytes on the CSPRNG path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_crypto_random_gate_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects platform entropy hooks instead of hardcoding x86' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_crypto_random_gate_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents that shimmed entropy is not production entropy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
