# Pattern Engine Specification

> Tests covering Rule schema — create_rule + rule_summary, cipher_rule_table — registry contents, lookup_rule_for_callee — known software callees, PatternCost — comparator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Engine Specification

## Scenarios

### Rule schema — create_rule + rule_summary

#### create_rule fills name, intrinsic, requires, cost_delta correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create_rule fills name, intrinsic, requires, cost_delta correctly
   - Expected: r.name equals `test_rule_aes`
   - Expected: r.intrinsic equals `crypto_aes_round`
   - Expected: r.required_fact equals `aes`
   - Expected: r.cost_delta equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("create_rule fills name, intrinsic, requires, cost_delta correctly")
val r = create_rule("test_rule_aes", "crypto_aes_round", "aes", -3)
expect(r.name).to_equal("test_rule_aes")
expect(r.intrinsic).to_equal("crypto_aes_round")
expect(r.required_fact).to_equal("aes")
expect(r.cost_delta).to_equal(-3)
```

</details>

#### rule_summary contains rule name and intrinsic substring

- rule_summary contains rule name and intrinsic substring
   - Expected: summary.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rule_summary contains rule name and intrinsic substring")
val r = create_rule("match_aes_round_software", "crypto_aes_round", "aes", -3)
val summary = rule_summary(r)
expect(summary.len() > 0).to_equal(true)
expect(summary).to_contain("match_aes_round_software")
expect(summary).to_contain("crypto_aes_round")
```

</details>

### cipher_rule_table — registry contents

#### returns at least 5 rules

- returns at least 5 rules
   - Expected: table.len() >= 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns at least 5 rules")
val table = cipher_rule_table()
expect(table.len() >= 5).to_equal(true)
```

</details>

#### each rule has non-empty name, non-empty intrinsic, non-empty requires

- each rule has non-empty name, non-empty intrinsic, non-empty requires
   - Expected: r.name.len() > 0 is true
   - Expected: r.intrinsic.len() > 0 is true
   - Expected: r.required_fact.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("each rule has non-empty name, non-empty intrinsic, non-empty requires")
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

- first rule is the AES round rule with intrinsic crypto_aes_round
   - Expected: first.intrinsic equals `CRYPTO_AES_ROUND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("first rule is the AES round rule with intrinsic crypto_aes_round")
val table = cipher_rule_table()
val first = table[0]
expect(first.intrinsic).to_equal(CRYPTO_AES_ROUND)
```

</details>

#### each rule cost_delta is negative (cheaper than scalar software)

- each rule cost_delta is negative (cheaper than scalar software)
   - Expected: r.cost_delta < 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("each rule cost_delta is negative (cheaper than scalar software)")
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

- aes_round_software callee returns Some(rule) with intrinsic crypto_aes_round
   - Expected: result != nil is true
   - Expected: r.intrinsic equals `CRYPTO_AES_ROUND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("aes_round_software callee returns Some(rule) with intrinsic crypto_aes_round")
val result = lookup_rule_for_callee("std.common.aes.cipher.aes_round_software")
expect(result != nil).to_equal(true)
val r = result.unwrap()
expect(r.intrinsic).to_equal(CRYPTO_AES_ROUND)
```

</details>

#### sha256 compress_block callee returns Some with crypto_sha256_rounds2

- sha256 compress_block callee returns Some with crypto_sha256_rounds2
   - Expected: result != nil is true
   - Expected: r.intrinsic equals `CRYPTO_SHA256_RNDS2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sha256 compress_block callee returns Some with crypto_sha256_rounds2")
val result = lookup_rule_for_callee("std.common.crypto.sha256.compress_block")
expect(result != nil).to_equal(true)
val r = result.unwrap()
expect(r.intrinsic).to_equal(CRYPTO_SHA256_RNDS2)
```

</details>

#### os crc32 update_u64 callee returns Some with crc32_u64

- os crc32 update_u64 callee returns Some with crc32_u64
   - Expected: result != nil is true
   - Expected: r.intrinsic equals `CRC32_U64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("os crc32 update_u64 callee returns Some with crc32_u64")
val result = lookup_rule_for_callee("os.crypto.crc32.update_u64")
expect(result != nil).to_equal(true)
val r = result.unwrap()
expect(r.intrinsic).to_equal(CRC32_U64)
```

</details>

#### unrecognised symbol returns nil

- unrecognised symbol returns nil
   - Expected: result != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unrecognised symbol returns nil")
val result = lookup_rule_for_callee("std.common.totally.unknown.callee")
expect(result != nil).to_equal(false)
```

</details>

#### cipher provider is built in for hot-path lookup

- cipher provider is built in for hot-path lookup
   - Expected: provider.name equals `cipher-pattern-rules`
   - Expected: provider.version equals `1.0.0`
   - Expected: provider.kind equals `OptimizerProviderKind.Pattern`
   - Expected: provider.load_mode equals `OptimizerRuleLoadMode.Builtin`
   - Expected: provider.lookup_kind equals `OptimizerRuleLookupKind.DirectExact`
   - Expected: optimization_rule_provider_should_embed(provider) is true
   - Expected: optimization_rule_provider_uses_direct_lookup(provider) is true
   - Expected: provider.safety_class equals `pure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("cipher provider is built in for hot-path lookup")
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

- dynamic providers are not embedded into the hot lookup path
   - Expected: provider.load_mode equals `OptimizerRuleLoadMode.DynamicLibrary`
   - Expected: provider.lookup_kind equals `OptimizerRuleLookupKind.DynamicExact`
   - Expected: optimization_rule_provider_should_embed(provider) is false
   - Expected: provider.safety_class equals `experimental`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dynamic providers are not embedded into the hot lookup path")
val provider = optimization_rule_provider_dynamic("rare-extra-rules", "build/plugins/rare-rules.so")
expect(provider.load_mode).to_equal(OptimizerRuleLoadMode.DynamicLibrary)
expect(provider.lookup_kind).to_equal(OptimizerRuleLookupKind.DynamicExact)
expect(optimization_rule_provider_should_embed(provider)).to_equal(false)
expect(provider.safety_class).to_equal("experimental")
```

</details>

#### pipeline providers declare facts and are distinguishable from direct lookup providers

- pipeline providers declare facts and are distinguishable from direct lookup providers
   - Expected: provider.name equals `simple.opt.server.io`
   - Expected: provider.kind equals `OptimizerProviderKind.Mir`
   - Expected: optimization_rule_provider_is_pipeline_pass(provider) is true
   - Expected: optimization_rule_provider_has_required_fact(provider, "io_alias_summary") is true
   - Expected: optimization_rule_provider_has_required_fact(provider, "missing_fact") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pipeline providers declare facts and are distinguishable from direct lookup providers")
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

- provider planning rejects missing facts without changing semantics
   - Expected: optimization_fact_list_contains(["typed_mir"], "typed_mir") is true
   - Expected: optimization_rule_provider_can_run(provider, ["typed_mir"]) is false
   - Expected: missing != nil is true
   - Expected: missing.unwrap() equals `io_alias_summary`
   - Expected: optimization_rule_provider_can_run(provider, ["typed_mir", "io_alias_summary"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provider planning rejects missing facts without changing semantics")
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
expect(missing != nil).to_equal(true)
expect(missing.unwrap()).to_equal("io_alias_summary")
expect(optimization_rule_provider_can_run(provider, ["typed_mir", "io_alias_summary"])).to_equal(true)
```

</details>

#### jit hotspot providers use the same plugin contract with runtime facts

- jit hotspot providers use the same plugin contract with runtime facts
   - Expected: provider.kind equals `OptimizerProviderKind.JitHotspot`
   - Expected: provider.load_mode equals `OptimizerRuleLoadMode.Builtin`
   - Expected: provider.lookup_kind equals `OptimizerRuleLookupKind.PipelinePass`
   - Expected: optimization_rule_provider_is_runtime_hotspot(provider) is true
   - Expected: optimization_rule_provider_can_run(provider, ["profile.hot_count", "typed_mir"]) is false
   - Expected: optimization_rule_provider_can_run(provider, ["profile.hot_count", "typed_mir", "safe_deopt"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("jit hotspot providers use the same plugin contract with runtime facts")
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

- backend policy keeps Simple-side canonicalization for Cranelift and skips it for LLVM
   - Expected: optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Cranelift) is true
   - Expected: optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Llvm) is false
   - Expected: optimization_rule_provider_applies_to_backend_name(planned, "cranlift") is true
   - Expected: reason != nil is true
   - Expected: reason.unwrap() equals `llvm_backend_runs_mem2reg_sroa_pipeline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend policy keeps Simple-side canonicalization for Cranelift and skips it for LLVM")
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
expect(reason != nil).to_equal(true)
expect(reason.unwrap()).to_equal("llvm_backend_runs_mem2reg_sroa_pipeline")
```

</details>

#### backend policy can restrict expensive hotspot rebuilds to one backend

- backend policy can restrict expensive hotspot rebuilds to one backend
   - Expected: optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Cranelift) is true
   - Expected: optimization_rule_provider_applies_to_backend(planned, OptimizerBackendKind.Llvm) is false
   - Expected: optimization_backend_kind_name(optimization_backend_kind_from_text("llvm")) equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend policy can restrict expensive hotspot rebuilds to one backend")
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

- exact lookup bindings support reusable non-cipher rule providers
   - Expected: hit != nil is true
   - Expected: hit.unwrap().intrinsic equals `math_abs`
   - Expected: miss != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("exact lookup bindings support reusable non-cipher rule providers")
val rule = create_rule("match_custom_abs", "math_abs", "scalar", -1)
val bindings = [create_exact_rule_binding("std.math.abs_software", rule)]
val hit = lookup_exact_rule_binding(bindings, "std.math.abs_software")
expect(hit != nil).to_equal(true)
expect(hit.unwrap().intrinsic).to_equal("math_abs")
val miss = lookup_exact_rule_binding(bindings, "std.math.sqrt")
expect(miss != nil).to_equal(false)
```

</details>

#### lookup stats count hit and miss without touching rule data

- lookup stats count hit and miss without touching rule data
   - Expected: two.lookups equals `2`
   - Expected: two.hits equals `1`
   - Expected: two.misses equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lookup stats count hit and miss without touching rule data")
val zero = rule_lookup_stats_zero()
val one = rule_lookup_stats_record(zero, true)
val two = rule_lookup_stats_record(one, false)
expect(two.lookups).to_equal(2)
expect(two.hits).to_equal(1)
expect(two.misses).to_equal(1)
```

</details>

#### provider stats count changed and skipped scopes

- provider stats count changed and skipped scopes
   - Expected: skipped.scopes equals `2`
   - Expected: skipped.rewrites equals `3`
   - Expected: skipped.skipped equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provider stats count changed and skipped scopes")
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

- lower-latency cost ranks better than higher-latency
   - Expected: pattern_cost_better(cheap, expensive) is true
   - Expected: pattern_cost_better(expensive, cheap) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lower-latency cost ranks better than higher-latency")
val cheap = PatternCost(latency: 2, code_size: 0, reg_pressure: 0, tail_cost: 0)
val expensive = PatternCost(latency: 8, code_size: 0, reg_pressure: 0, tail_cost: 0)
expect(pattern_cost_better(cheap, expensive)).to_equal(true)
expect(pattern_cost_better(expensive, cheap)).to_equal(false)
```

</details>

#### identical costs are not better than each other

- identical costs are not better than each other
   - Expected: pattern_cost_better(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identical costs are not better than each other")
val a = PatternCost(latency: 4, code_size: 1, reg_pressure: 2, tail_cost: 0)
val b = PatternCost(latency: 4, code_size: 1, reg_pressure: 2, tail_cost: 0)
expect(pattern_cost_better(a, b)).to_equal(false)
```

</details>

#### pattern_cost_total weights latency more than reg_pressure

- pattern_cost_total weights latency more than reg_pressure
   - Expected: total_lat > total_pres is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pattern_cost_total weights latency more than reg_pressure")
val high_latency = PatternCost(latency: 4, code_size: 0, reg_pressure: 0, tail_cost: 0)
val high_pressure = PatternCost(latency: 0, code_size: 0, reg_pressure: 4, tail_cost: 0)
# latency weight=4, reg_pressure weight=2 → 4*4=16 vs 4*2=8
val total_lat = pattern_cost_total(high_latency)
val total_pres = pattern_cost_total(high_pressure)
expect(total_lat > total_pres).to_equal(true)
```

</details>

#### pattern_cost_default returns a zero-cost tuple

- pattern_cost_default returns a zero-cost tuple
   - Expected: c.latency equals `0`
   - Expected: c.code_size equals `0`
   - Expected: c.reg_pressure equals `0`
   - Expected: c.tail_cost equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pattern_cost_default returns a zero-cost tuple")
val c = pattern_cost_default()
expect(c.latency).to_equal(0)
expect(c.code_size).to_equal(0)
expect(c.reg_pressure).to_equal(0)
expect(c.tail_cost).to_equal(0)
```

</details>

#### pattern_cost_total of default is zero

- pattern_cost_total of default is zero
   - Expected: pattern_cost_total(c) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pattern_cost_total of default is zero")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Rule schema — create_rule + rule_summary, cipher_rule_table — registry contents, lookup_rule_for_callee — known software callees, PatternCost — comparator.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `955a57608c1185181a2f4b63dca840aaa3347c4e42ea04c90c9c165f09acec7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `955a57608c1185181a2f4b63dca840aaa3347c4e42ea04c90c9c165f09acec7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `955a57608c1185181a2f4b63dca840aaa3347c4e42ea04c90c9c165f09acec7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_rule fills name, intrinsic, requires, cost_delta correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rule_summary contains rule name and intrinsic substring' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns at least 5 rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
