# Encode Riscv64 Specification

> <details>

<!-- sdn-diagram:id=encode_riscv64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_riscv64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_riscv64_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_riscv64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode Riscv64 Specification

## Scenarios

### Encode Riscv64

#### shares the Linux call relocation and ABI contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(R_RISCV_CALL_PLT).to_equal(19)
expect(contract.call_plt_reloc).to_equal(19)
expect(contract.abi_text()).to_equal("lp64d")
expect(contract.march).to_equal("rv64gc")
```

</details>

### Encode Riscv64 scalar bitmanip

#### encodes rol

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_rol_riscv64(1, 2, 3)).to_equal([0xB3, 0x10, 0x31, 0x60])
```

</details>

#### encodes ror

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_ror_riscv64(1, 2, 3)).to_equal([0xB3, 0x50, 0x31, 0x60])
```

</details>

#### encodes clz/ctz/cpop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_clz_riscv64(1, 2)).to_equal([0x93, 0x10, 0x01, 0x60])
expect(emit_ctz_riscv64(1, 2)).to_equal([0x93, 0x10, 0x11, 0x60])
expect(emit_cpop_riscv64(1, 2)).to_equal([0x93, 0x10, 0x21, 0x60])
```

</details>

#### encodes rev8 and brev8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_rev8_riscv64(1, 2)).to_equal([0x93, 0x50, 0x81, 0x6B])
expect(emit_brev8_riscv64(1, 2)).to_equal([0x93, 0x50, 0x71, 0x68])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/encode_riscv64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Encode Riscv64
- Encode Riscv64 scalar bitmanip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
