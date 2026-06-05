# Opt Remark Specification

> <details>

<!-- sdn-diagram:id=opt_remark_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opt_remark_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opt_remark_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opt_remark_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opt Remark Specification

## Scenarios

### pattern_idiom_stats_with_remark — cipher_remark=true

#### returns stats with cipher_remark set to true

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = pattern_idiom_stats_with_remark()
expect(s.cipher_remark).to_equal(true)
```

</details>

#### starts with zero cipher_hits

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = pattern_idiom_stats_with_remark()
expect(s.cipher_hits).to_equal(0)
```

</details>

### pattern_idiom_stats_zero — cipher_remark=false

#### returns stats with cipher_remark set to false

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = pattern_idiom_stats_zero()
expect(s.cipher_remark).to_equal(false)
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + AES callee

#### instruction becomes Intrinsic when cipher_remark=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

#### intrinsic name is crypto_aes_round when cipher_remark=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val intrinsic_name = match inst.kind:
    case Intrinsic(dest, name, args): name
    case _: ""
expect(intrinsic_name).to_equal("crypto_aes_round")
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=false + AES caps + AES callee

#### instruction still becomes Intrinsic when cipher_remark=false

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=true + no caps + AES callee

#### instruction stays Call when caps lack AES

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + non-cipher callee

#### instruction stays Call for non-cipher callee

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.io.print")
val caps = make_x86_caps_aes()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — SHA256 callee + sha_ni caps + cipher_remark=true

#### SHA256 call becomes Intrinsic with sha_ni caps and cipher_remark=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.crypto.sha256.compress_block")
val caps = make_x86_caps_sha_ni()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

### run_pattern_idiom_pass_x86 — CRC32 callee + sse42 caps + cipher_remark=true

#### CRC32 call becomes Intrinsic with sse42 caps and cipher_remark=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.crypto.crc32.update_byte")
val caps = make_x86_caps_sse42()
val out  = run_pattern_idiom_pass_x86(m, caps, true)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_intrinsic = match inst.kind:
    case Intrinsic(dest, name, args): true
    case _: false
expect(is_intrinsic).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/opt_remark_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pattern_idiom_stats_with_remark — cipher_remark=true
- pattern_idiom_stats_zero — cipher_remark=false
- run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + AES callee
- run_pattern_idiom_pass_x86 — cipher_remark=false + AES caps + AES callee
- run_pattern_idiom_pass_x86 — cipher_remark=true + no caps + AES callee
- run_pattern_idiom_pass_x86 — cipher_remark=true + AES caps + non-cipher callee
- run_pattern_idiom_pass_x86 — SHA256 callee + sha_ni caps + cipher_remark=true
- run_pattern_idiom_pass_x86 — CRC32 callee + sse42 caps + cipher_remark=true

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
