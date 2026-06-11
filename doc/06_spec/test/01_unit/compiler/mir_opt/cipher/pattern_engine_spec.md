# Pattern Engine Specification

> <details>

<!-- sdn-diagram:id=pattern_engine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_engine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_engine_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_engine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Engine Specification

## Scenarios

### Rule schema — create_rule + rule_summary

#### create_rule fills name, intrinsic, requires, cost_delta correctly

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = create_rule("test_rule_aes", "crypto_aes_round", "aes", -3)
expect(r.name).to_equal("test_rule_aes")
expect(r.intrinsic).to_equal("crypto_aes_round")
expect(r.required_fact).to_equal("aes")
expect(r.cost_delta).to_equal(-3)
```

</details>

#### rule_summary contains rule name and intrinsic substring

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = create_rule("match_aes_round_software", "crypto_aes_round", "aes", -3)
val summary = rule_summary(r)
expect(summary.len() > 0).to_equal(true)
expect(summary).to_contain("match_aes_round_software")
expect(summary).to_contain("crypto_aes_round")
```

</details>

### cipher_rule_table — registry contents

#### returns at least 5 rules

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = cipher_rule_table()
expect(table.len() >= 5).to_equal(true)
```

</details>

#### each rule has non-empty name, non-empty intrinsic, non-empty requires

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = cipher_rule_table()
var i = 0
while i < table.len():
    val r = table[i]
    expect(r.name.len() > 0).to_equal(true)
    expect(r.intrinsic.len() > 0).to_equal(true)
    expect(r.required_fact.len() > 0).to_equal(true)
    i = i + 1
```

</details>

#### first rule is the AES round rule with intrinsic crypto_aes_round

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = cipher_rule_table()
val first = table[0]
expect(first.intrinsic).to_equal(CRYPTO_AES_ROUND)
```

</details>

#### each rule cost_delta is negative (cheaper than scalar software)

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = cipher_rule_table()
var i = 0
while i < table.len():
    val r = table[i]
    expect(r.cost_delta < 0).to_equal(true)
    i = i + 1
```

</details>

### lookup_rule_for_callee — known software callees

#### aes_round_software callee returns Some(rule) with intrinsic crypto_aes_round

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lookup_rule_for_callee("std.common.aes.cipher.aes_round_software")
expect(result.?).to_equal(true)
val r = result.unwrap()
expect(r.intrinsic).to_equal(CRYPTO_AES_ROUND)
```

</details>

#### sha256 compress_block callee returns Some with crypto_sha256_rounds2

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lookup_rule_for_callee("std.common.crypto.sha256.compress_block")
expect(result.?).to_equal(true)
val r = result.unwrap()
expect(r.intrinsic).to_equal(CRYPTO_SHA256_RNDS2)
```

</details>

#### os crc32 update_u64 callee returns Some with crc32_u64

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lookup_rule_for_callee("os.crypto.crc32.update_u64")
expect(result.?).to_equal(true)
val r = result.unwrap()
expect(r.intrinsic).to_equal(CRC32_U64)
```

</details>

#### unrecognised symbol returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lookup_rule_for_callee("std.common.totally.unknown.callee")
expect(result.?).to_equal(false)
```

</details>

#### cipher provider is built in for hot-path lookup

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = cipher_rule_provider()
expect(provider.name).to_equal("cipher-pattern-rules")
expect(provider.version).to_equal("1.0.0")
expect(provider.kind).to_equal(OptimizerProviderKind.Pattern)
expect(provider.load_mode).to_equal(OptimizerRuleLoadMode.Builtin)
expect(provider.lookup_kind).to_equal(OptimizerRuleLookupKind.DirectExact)
expect(optimization_rule_provider_should_embed(provider)).to_equal(true)
expect(optimization_rule_provider_uses_direct_lookup(provider)).to_equal(true)
expect(provider.safety_class).to_equal("pure")
```

</details>

#### dynamic providers are not embedded into the hot lookup path

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_dynamic("rare-extra-rules", "build/plugins/rare-rules.so")
expect(provider.load_mode).to_equal(OptimizerRuleLoadMode.DynamicLibrary)
expect(provider.lookup_kind).to_equal(OptimizerRuleLookupKind.DynamicExact)
expect(optimization_rule_provider_should_embed(provider)).to_equal(false)
expect(provider.safety_class).to_equal("experimental")
```

</details>

#### pipeline providers declare facts and are distinguishable from direct lookup providers

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_with_contract(
    "simple.opt.server.io",
    OptimizerProviderKind.Mir,
    OptimizerRuleLookupKind.PipelinePass,
    true,
    ["typed_mir", "io_alias_summary"],
    ["canonical_mir"],
    "pure"
)
expect(provider.name).to_equal("simple.opt.server.io")
expect(provider.kind).to_equal(OptimizerProviderKind.Mir)
expect(optimization_rule_provider_is_pipeline_pass(provider)).to_equal(true)
expect(optimization_rule_provider_has_required_fact(provider, "io_alias_summary")).to_equal(true)
expect(optimization_rule_provider_has_required_fact(provider, "missing_fact")).to_equal(false)
```

</details>

#### provider planning rejects missing facts without changing semantics

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_with_contract(
    "simple.opt.server.io",
    OptimizerProviderKind.Mir,
    OptimizerRuleLookupKind.PipelinePass,
    true,
    ["typed_mir", "io_alias_summary"],
    ["canonical_mir"],
    "pure"
)
expect(optimization_fact_list_contains(["typed_mir"], "typed_mir")).to_equal(true)
expect(optimization_rule_provider_can_run(provider, ["typed_mir"])).to_equal(false)
val missing = optimization_rule_provider_missing_fact(provider, ["typed_mir"])
expect(missing.?).to_equal(true)
expect(missing.unwrap()).to_equal("io_alias_summary")
expect(optimization_rule_provider_can_run(provider, ["typed_mir", "io_alias_summary"])).to_equal(true)
```

</details>

#### jit hotspot providers use the same plugin contract with runtime facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_jit_hotspot(
    "simple.opt.jit.hotspot.loop-body",
    ["profile.hot_count", "typed_mir", "safe_deopt"],
    ["jit.hotspot_plan"],
    "runtime-guarded"
)
expect(provider.kind).to_equal(OptimizerProviderKind.JitHotspot)
expect(provider.load_mode).to_equal(OptimizerRuleLoadMode.Builtin)
expect(provider.lookup_kind).to_equal(OptimizerRuleLookupKind.PipelinePass)
expect(optimization_rule_provider_is_runtime_hotspot(provider)).to_equal(true)
expect(optimization_rule_provider_can_run(provider, ["profile.hot_count", "typed_mir"])).to_equal(false)
expect(optimization_rule_provider_can_run(provider, ["profile.hot_count", "typed_mir", "safe_deopt"])).to_equal(true)
```

</details>

#### backend policy keeps Simple-side canonicalization for Cranelift and skips it for LLVM

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_jit_hotspot(
    "simple.opt.jit.hotspot.ssa-var-canon",
    ["profile.hot_count", "typed_mir", "safe_deopt"],
    ["jit.hotspot_plan"],
    "runtime-guarded"
)
val policy = optimization_backend_policy_skip(
    [OptimizerBackendKind.Llvm],
    "llvm_backend_runs_mem2reg_sroa_pipeline"
)
val planned = optimization_rule_provider_with_backend_policy(provider, policy)

expect(optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Cranelift)).to_equal(true)
expect(optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Llvm)).to_equal(false)
expect(optimization_rule_provider_applies_to_backend_name(planned, "cranlift")).to_equal(true)
val reason = optimization_rule_provider_skip_reason(planned, OptimizerBackendKind.Llvm)
expect(reason.?).to_equal(true)
expect(reason.unwrap()).to_equal("llvm_backend_runs_mem2reg_sroa_pipeline")
```

</details>

#### backend policy can restrict expensive hotspot rebuilds to one backend

1. optimization backend policy only
   - Expected: optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Cranelift) is true
   - Expected: optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Llvm) is false
   - Expected: optimization_backend_kind_name(optimization_backend_kind_from_text("llvm")) equals `llvm`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_jit_hotspot(
    "simple.opt.jit.hotspot.cranelift-rebuild",
    ["profile.hot_count", "typed_mir", "safe_deopt"],
    ["jit.hotspot_plan"],
    "runtime-guarded"
)
val planned = optimization_rule_provider_with_backend_policy(
    provider,
    optimization_backend_policy_only([OptimizerBackendKind.Cranelift], "cranelift_needs_simple_preopt")
)

expect(optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Cranelift)).to_equal(true)
expect(optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Llvm)).to_equal(false)
expect(optimization_backend_kind_name(optimization_backend_kind_from_text("llvm"))).to_equal("llvm")
```

</details>

#### exact lookup bindings support reusable non-cipher rule providers

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = create_rule("match_custom_abs", "math_abs", "scalar", -1)
val bindings = [create_exact_rule_binding("std.math.abs_software", rule)]
val hit = lookup_exact_rule_binding(bindings, "std.math.abs_software")
expect(hit.?).to_equal(true)
expect(hit.unwrap().intrinsic).to_equal("math_abs")
val miss = lookup_exact_rule_binding(bindings, "std.math.sqrt")
expect(miss.?).to_equal(false)
```

</details>

#### lookup stats count hit and miss without touching rule data

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = rule_lookup_stats_zero()
val one = rule_lookup_stats_record(zero, true)
val two = rule_lookup_stats_record(one, false)
expect(two.lookups).to_equal(2)
expect(two.hits).to_equal(1)
expect(two.misses).to_equal(1)
```

</details>

#### provider stats count changed and skipped scopes

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = optimization_provider_stats_zero()
val changed = optimization_provider_stats_record_scope(zero, 3)
val skipped = optimization_provider_stats_record_scope(changed, 0)
expect(skipped.scopes).to_equal(2)
expect(skipped.rewrites).to_equal(3)
expect(skipped.skipped).to_equal(1)
```

</details>

### PatternCost — comparator

#### lower-latency cost ranks better than higher-latency

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cheap = PatternCost(latency: 2, code_size: 0, reg_pressure: 0, tail_cost: 0)
val expensive = PatternCost(latency: 8, code_size: 0, reg_pressure: 0, tail_cost: 0)
expect(pattern_cost_better(cheap, expensive)).to_equal(true)
expect(pattern_cost_better(expensive, cheap)).to_equal(false)
```

</details>

#### identical costs are not better than each other

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = PatternCost(latency: 4, code_size: 1, reg_pressure: 2, tail_cost: 0)
val b = PatternCost(latency: 4, code_size: 1, reg_pressure: 2, tail_cost: 0)
expect(pattern_cost_better(a, b)).to_equal(false)
```

</details>

#### pattern_cost_total weights latency more than reg_pressure

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val high_latency = PatternCost(latency: 4, code_size: 0, reg_pressure: 0, tail_cost: 0)
val high_pressure = PatternCost(latency: 0, code_size: 0, reg_pressure: 4, tail_cost: 0)
# latency weight=4, reg_pressure weight=2 → 4*4=16 vs 4*2=8
val total_lat = pattern_cost_total(high_latency)
val total_pres = pattern_cost_total(high_pressure)
expect(total_lat > total_pres).to_equal(true)
```

</details>

#### pattern_cost_default returns a zero-cost tuple

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = pattern_cost_default()
expect(c.latency).to_equal(0)
expect(c.code_size).to_equal(0)
expect(c.reg_pressure).to_equal(0)
expect(c.tail_cost).to_equal(0)
```

</details>

#### pattern_cost_total of default is zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = pattern_cost_default()
expect(pattern_cost_total(c)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Rule schema — create_rule + rule_summary
- cipher_rule_table — registry contents
- lookup_rule_for_callee — known software callees
- PatternCost — comparator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
