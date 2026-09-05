# Simpleos Crypto Random Gate Specification

> <details>

<!-- sdn-diagram:id=simpleos_crypto_random_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_crypto_random_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_crypto_random_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_crypto_random_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Crypto Random Gate Specification

## Scenarios

### SimpleOS crypto random production gate

#### keeps public random_bytes on the CSPRNG path

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/os/crypto/random.spl")

expect(source).to_contain("fn random_bytes(count: u64) -> [u8]")
expect(source).to_contain("if not g_csprng.initialized:")
expect(source).to_contain("_csprng_init()")
expect(source.contains("_soft_random_u64")).to_equal(false)
expect(source.contains("return host_bytes")).to_equal(false)
```

</details>

#### selects platform entropy hooks instead of hardcoding x86

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/os/crypto/random.spl")
val shim = rt_file_read_text("src/os/kernel/net/tls_shim.spl")

expect(source).to_contain("not a production entropy source")
expect(shim).to_contain("NOT cryptographically secure")
```

</details>

#### uses RISC-V CSR jitter instead of the LCG for rt_riscv_seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shim = rt_file_read_text("src/os/kernel/net/tls_shim.spl")
val entropy = rt_file_read_text("src/os/kernel/arch/riscv64/entropy.spl")

expect(shim).to_contain("fn rt_riscv_seed() -> u64")
expect(shim).to_contain("csrr_cycle()")
expect(shim).to_contain("csrr_time()")
expect(shim).to_contain("csrr_instret()")
expect(entropy).to_contain("cycle+time+instret")
```

</details>

#### keeps x86_64 baremetal rt_rdrand on the CPUID-gated hardware path

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = rt_file_read_text("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")

expect(runtime).to_contain("spl_i64 rt_entropy_hardware_ready(void)")
expect(runtime).to_contain("RISC-V TLS remains blocked")
expect(runtime).to_contain("return 0;")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_crypto_random_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
