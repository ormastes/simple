# Pattern Dispatch Specification

> <details>

<!-- sdn-diagram:id=pattern_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_dispatch_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Dispatch Specification

## Scenarios

### PatternIdiomStats — zero builder

#### starts with zero visited functions

- var s = pattern idiom stats zero
   - Expected: s.visited_functions equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = pattern_idiom_stats_zero()
expect(s.visited_functions).to_equal(0)
```

</details>

#### starts with zero visited blocks

- var s = pattern idiom stats zero
   - Expected: s.visited_blocks equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = pattern_idiom_stats_zero()
expect(s.visited_blocks).to_equal(0)
```

</details>

#### starts with zero visited calls

- var s = pattern idiom stats zero
   - Expected: s.visited_calls equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = pattern_idiom_stats_zero()
expect(s.visited_calls).to_equal(0)
```

</details>

#### starts with zero cipher hits

- var s = pattern idiom stats zero
   - Expected: s.cipher_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = pattern_idiom_stats_zero()
expect(s.cipher_hits).to_equal(0)
```

</details>

### pattern idiom capability guards

#### x86 all-false caps do not support any pattern idiom

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = make_x86_caps_none()
expect(x86_caps_supports_any_pattern_idiom(caps)).to_equal(false)
```

</details>

#### x86 AES caps support pattern idioms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = make_x86_caps_aes_only()
expect(x86_caps_supports_any_pattern_idiom(caps)).to_equal(true)
```

</details>

#### TargetCapsKind.None_ does not support pattern idioms

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(caps_kind_supports_any_pattern_idiom(TargetCapsKind.None_)).to_equal(false)
```

</details>

#### default run_pattern_idiom_pass preserves a cipher call through fast no-op path

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_call_module("std.common.aes.cipher.aes_round_software")
val out = run_pattern_idiom_pass(m)
val sym = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

### idiom_for_intrinsic — known cipher intrinsics

#### crypto_aes_round maps to AesEnc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = idiom_for_intrinsic("crypto_aes_round")
expect(result.?).to_equal(true)
```

</details>

#### crypto_aes_round_last maps to AesEncLast

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = idiom_for_intrinsic("crypto_aes_round_last")
expect(result.?).to_equal(true)
```

</details>

#### crc32_u8 maps to Crc32U8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = idiom_for_intrinsic("crc32_u8")
expect(result.?).to_equal(true)
```

</details>

#### clmul_lo maps to ClmulLo

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = idiom_for_intrinsic("clmul_lo")
expect(result.?).to_equal(true)
```

</details>

#### unknown name returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = idiom_for_intrinsic("not_a_cipher")
expect(result.?).to_equal(false)
```

</details>

#### empty string returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = idiom_for_intrinsic("")
expect(result.?).to_equal(false)
```

</details>

### run_pattern_idiom_pass_x86 — rewrites AES call when has_aes=true

#### module function count is preserved after rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes_only()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

#### rewritten block has same instruction count as original

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes_only()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

#### rewritten instruction is Intrinsic not Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes_only()
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

#### intrinsic name is crypto_aes_round after rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_aes_only()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val intrinsic_name = match inst.kind:
    case Intrinsic(dest, name, args): name
    case _: ""
expect(intrinsic_name).to_equal("crypto_aes_round")
```

</details>

### run_pattern_idiom_pass_x86 — no rewrite when has_aes=false

#### instruction remains Call when has_aes=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

#### block instruction count is unchanged when no rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.common.aes.cipher.aes_round_software")
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

### run_pattern_idiom_pass_x86 — no rewrite for non-cipher callee

#### instruction remains Call for std.io.print callee

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.io.print")
val caps = make_x86_caps_aes_only()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

#### block instruction count is unchanged for non-cipher callee

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module("std.io.print")
val caps = make_x86_caps_aes_only()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/pattern_dispatch_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PatternIdiomStats — zero builder
- pattern idiom capability guards
- idiom_for_intrinsic — known cipher intrinsics
- run_pattern_idiom_pass_x86 — rewrites AES call when has_aes=true
- run_pattern_idiom_pass_x86 — no rewrite when has_aes=false
- run_pattern_idiom_pass_x86 — no rewrite for non-cipher callee

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
