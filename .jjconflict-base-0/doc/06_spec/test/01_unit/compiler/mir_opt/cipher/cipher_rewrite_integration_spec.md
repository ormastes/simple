# Cipher Rewrite Integration Specification

> <details>

<!-- sdn-diagram:id=cipher_rewrite_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cipher_rewrite_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cipher_rewrite_integration_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cipher_rewrite_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cipher Rewrite Integration Specification

## Scenarios

### integration — two AES calls in one block with has_aes=true

#### instruction count is preserved after rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_on()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(func.blocks[0].instructions.len()).to_equal(2)
```

</details>

#### instruction at position 0 becomes Intrinsic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_on()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Intrinsic")
```

</details>

#### instruction at position 1 becomes Intrinsic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_on()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 1)).to_equal("Intrinsic")
```

</details>

#### both instructions are Intrinsic — indirect cipher_hits=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_on()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_count_intrinsic(func, 0)).to_equal(2)
```

</details>

#### position 0 intrinsic name is crypto_aes_round

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_on()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_intrinsic_name(func, 0, 0)).to_equal("crypto_aes_round")
```

</details>

#### position 1 intrinsic name is crypto_aes_round

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_on()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_intrinsic_name(func, 0, 1)).to_equal("crypto_aes_round")
```

</details>

### integration — two AES calls in one block with has_aes=false

#### instruction count is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_off()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(func.blocks[0].instructions.len()).to_equal(2)
```

</details>

#### instruction at position 0 remains Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_off()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Call")
```

</details>

#### instruction at position 1 remains Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_off()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 1)).to_equal("Call")
```

</details>

#### zero Intrinsic instructions — indirect cipher_hits=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_off()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_count_intrinsic(func, 0)).to_equal(0)
```

</details>

#### both instructions remain Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_aes_caps_off()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_count_call(func, 0)).to_equal(2)
```

</details>

### integration — multi-block function with AES call in each block

#### function block count is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(func.blocks.len()).to_equal(2)
```

</details>

#### block 0 instruction is rewritten to Intrinsic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Intrinsic")
```

</details>

#### block 1 instruction is rewritten to Intrinsic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 1, 0)).to_equal("Intrinsic")
```

</details>

#### block 0 instruction count preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

#### block 1 instruction count preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(func.blocks[1].instructions.len()).to_equal(1)
```

</details>

#### caps=off: block 0 remains Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Call")
```

</details>

#### caps=off: block 1 remains Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 1, 0)).to_equal("Call")
```

</details>

### integration — mixed block sizes: 1 inst + 2 inst across blocks

#### block 0 has 1 instruction after pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_mixed_block_sizes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

#### block 1 has 2 instructions after pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_mixed_block_sizes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(func.blocks[1].instructions.len()).to_equal(2)
```

</details>

#### block 0 instruction is Intrinsic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_mixed_block_sizes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Intrinsic")
```

</details>

#### block 1 both instructions are Intrinsic — count=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_mixed_block_sizes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_count_intrinsic(func, 1)).to_equal(2)
```

</details>

### integration — cipher_remark flag does not change rewrite result

#### with remark=true and caps on, cipher call is rewritten

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_single_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), true)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Intrinsic")
```

</details>

#### with remark=false and caps on, cipher call is rewritten

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_single_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Intrinsic")
```

</details>

#### with remark=true and caps off, cipher call is not rewritten

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_single_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), true)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Call")
```

</details>

#### with remark=false and caps off, cipher call is not rewritten

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_single_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_all_off(), false)
val func = intg_first_func(res)
expect(intg_inst_kind_tag(func, 0, 0)).to_equal("Call")
```

</details>

#### remark=true two-block: intrinsic name is crypto_aes_round in block 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = intg_module_two_blocks_aes()
val res  = run_pattern_idiom_pass_x86(m, intg_caps_aes_on(), true)
val func = intg_first_func(res)
expect(intg_inst_intrinsic_name(func, 0, 0)).to_equal("crypto_aes_round")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/cipher_rewrite_integration_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- integration — two AES calls in one block with has_aes=true
- integration — two AES calls in one block with has_aes=false
- integration — multi-block function with AES call in each block
- integration — mixed block sizes: 1 inst + 2 inst across blocks
- integration — cipher_remark flag does not change rewrite result

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
