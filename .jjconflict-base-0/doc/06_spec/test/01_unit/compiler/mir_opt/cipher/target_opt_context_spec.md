# Target Opt Context Specification

> <details>

<!-- sdn-diagram:id=target_opt_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_opt_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_opt_context_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_opt_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Opt Context Specification

## Scenarios

### target_opt_context_default — returns all-false caps

#### x86_caps.has_aes is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.x86_caps.has_aes).to_equal(false)
```

</details>

#### x86_caps.has_sha_ni is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.x86_caps.has_sha_ni).to_equal(false)
```

</details>

#### x86_caps.has_sse42 is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.x86_caps.has_sse42).to_equal(false)
```

</details>

#### x86_caps.has_pclmul is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.x86_caps.has_pclmul).to_equal(false)
```

</details>

#### x86_caps.has_avx2 is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.x86_caps.has_avx2).to_equal(false)
```

</details>

#### x86_caps.has_avx512 is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.x86_caps.has_avx512).to_equal(false)
```

</details>

#### cipher_remark is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = target_opt_context_default()
expect(ctx.cipher_remark).to_equal(false)
```

</details>

### optimizationpipeline_for_level — pipeline has target_ctx

#### NoOpt pipeline has target_ctx with all-false caps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.NoOpt)
expect(pipeline.target_ctx.x86_caps.has_aes).to_equal(false)
```

</details>

#### Size pipeline has target_ctx with cipher_remark=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.Size)
expect(pipeline.target_ctx.cipher_remark).to_equal(false)
```

</details>

#### Speed pipeline has target_ctx with has_avx2=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.Speed)
expect(pipeline.target_ctx.x86_caps.has_avx2).to_equal(false)
```

</details>

#### Aggressive pipeline has target_ctx with has_aes=false by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.Aggressive)
expect(pipeline.target_ctx.x86_caps.has_aes).to_equal(false)
```

</details>

### optimizationpipeline_for_level(Aggressive) — pass list

#### Aggressive passes include pattern_idiom

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.Aggressive)
expect(pipeline.passes.contains("pattern_idiom")).to_equal(true)
```

</details>

#### Speed passes include pattern_idiom

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.Speed)
expect(pipeline.passes.contains("pattern_idiom")).to_equal(true)
```

</details>

#### NoOpt passes list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = optimizationpipeline_for_level(OptLevel.NoOpt)
expect(pipeline.passes.len()).to_equal(0)
```

</details>

### optimize_module with NoOpt — module unchanged

#### function count is preserved after NoOpt optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val out = optimize_module(m, OptLevel.NoOpt)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

#### block instruction count is preserved with NoOpt

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val out = optimize_module(m, OptLevel.NoOpt)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

### pipeline_optimize with AES caps — rewrites aes_round via unified path

#### function count is preserved after rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = TargetOptContext(x86_caps: make_x86_caps_aes_only(), cipher_remark: false, caps_kind: TargetCapsKind.X86(make_x86_caps_aes_only()))
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

#### rewritten block has same instruction count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = TargetOptContext(x86_caps: make_x86_caps_aes_only(), cipher_remark: false, caps_kind: TargetCapsKind.X86(make_x86_caps_aes_only()))
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

#### rewritten instruction is Intrinsic not Call

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = TargetOptContext(x86_caps: make_x86_caps_aes_only(), cipher_remark: false, caps_kind: TargetCapsKind.X86(make_x86_caps_aes_only()))
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = TargetOptContext(x86_caps: make_x86_caps_aes_only(), cipher_remark: false, caps_kind: TargetCapsKind.X86(make_x86_caps_aes_only()))
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val intrinsic_name = match inst.kind:
    case Intrinsic(dest, name, args): name
    case _: ""
expect(intrinsic_name).to_equal("crypto_aes_round")
```

</details>

### pipeline_optimize with no AES caps — Call stays Call

#### instruction remains Call when has_aes=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = TargetOptContext(x86_caps: make_x86_caps_none(), cipher_remark: false, caps_kind: TargetCapsKind.X86(make_x86_caps_none()))
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

#### block instruction count unchanged when no rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = TargetOptContext(x86_caps: make_x86_caps_none(), cipher_remark: false, caps_kind: TargetCapsKind.X86(make_x86_caps_none()))
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

### pipeline_optimize with default ctx — no cipher rewrite

#### instruction remains Call with default target_opt_context

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = target_opt_context_default()
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val inst = func.blocks[0].instructions[0]
val is_call = match inst.kind:
    case Call(dest, func_op, args): true
    case _: false
expect(is_call).to_equal(true)
```

</details>

#### function count is preserved with default ctx

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m   = make_call_module("std.common.aes.cipher.aes_round_software")
val ctx = target_opt_context_default()
val pipeline = OptimizationPipeline(level: OptLevel.Aggressive, passes: ["pattern_idiom"], target_ctx: ctx)
val out = pipeline_optimize(pipeline, m)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/target_opt_context_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- target_opt_context_default — returns all-false caps
- optimizationpipeline_for_level — pipeline has target_ctx
- optimizationpipeline_for_level(Aggressive) — pass list
- optimize_module with NoOpt — module unchanged
- pipeline_optimize with AES caps — rewrites aes_round via unified path
- pipeline_optimize with no AES caps — Call stays Call
- pipeline_optimize with default ctx — no cipher rewrite

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
