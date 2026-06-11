# Aop Log Policy Specification

> <details>

<!-- sdn-diagram:id=aop_log_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_log_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_log_policy_spec -> std
aop_log_policy_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_log_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Log Policy Specification

## Scenarios

### AOP Log Policy

#### classifies hardware joins for audit logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = aop_log_join_kind("lib.hardware.uart", "write_register", [], [])
expect(kind).to_equal("hardware")
expect(aop_log_should_weave(kind, "release", false)).to_equal(true)
```

</details>

#### classifies external access joins for audit logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = aop_log_join_kind("app.net.client", "open_socket", [], ["network"])
expect(kind).to_equal("external_access")
expect(aop_log_should_weave(kind, "release", false)).to_equal(true)
```

</details>

#### omits trace instrumentation in release unless enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = aop_log_join_kind("runtime.trace.writer", "record_span", [], [])
expect(kind).to_equal("trace")
expect(aop_log_should_weave(kind, "release", false)).to_equal(false)
expect(aop_log_should_weave(kind, "release", true)).to_equal(true)
```

</details>

#### keeps debug joins out of release by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = aop_log_join_kind("app.cli.query", "parse_args", [], [])
expect(kind).to_equal("debug")
expect(aop_log_should_weave(kind, "release", false)).to_equal(false)
expect(aop_log_should_weave(kind, "debug", false)).to_equal(true)
```

</details>

#### publishes stable pointcut templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pointcut = aop_log_pointcut_for_kind("hardware")
expect(pointcut).to_contain("effect:hardware")
```

</details>

#### keeps AOP debug instrumentation globally disabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AopLogInstrumentationConfig.disabled()
expect(cfg.compile_log_level).to_equal("debug")
expect(aop_log_should_instrument_function_call(cfg)).to_equal(false)
expect(aop_log_should_instrument_variable_assignment(cfg)).to_equal(false)
```

</details>

#### enables function-call and variable-assignment instrumentation separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls_only = AopLogInstrumentationConfig.for_debug(true, false)
expect(aop_log_should_instrument_function_call(calls_only)).to_equal(true)
expect(aop_log_should_instrument_variable_assignment(calls_only)).to_equal(false)

val assigns_only = AopLogInstrumentationConfig.for_debug(false, true)
expect(aop_log_should_instrument_function_call(assigns_only)).to_equal(false)
expect(aop_log_should_instrument_variable_assignment(assigns_only)).to_equal(true)
```

</details>

#### allows compile and runtime levels to differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AopLogInstrumentationConfig.for_debug(true, true)
val compile_off = aop_log_with_compile_level(cfg, "off")
val runtime_warn = aop_log_with_runtime_level(compile_off, "warn")
expect(runtime_warn.compile_log_level).to_equal("off")
expect(runtime_warn.runtime_log_level).to_equal("warn")
expect(aop_log_should_instrument_function_call(runtime_warn)).to_equal(false)
expect(aop_log_should_instrument_variable_assignment(runtime_warn)).to_equal(false)
```

</details>

#### builds call-only weaving rules that match MIR call join points

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = aop_log_weaving_config(AopLogInstrumentationConfig.for_debug(true, false))
val blocks = [MirBlockInfo(id: 0, instruction_kinds: [InstructionInfo(index: 3, kind_tag: "call")])]
val result = weave_function(config, "run", "app.debug", [], [], blocks)
expect(result.advices_inserted).to_equal(1)
expect(result.advice_calls[0].join_point_kind).to_equal(JoinPointKind.FunctionCall)
expect(result.advice_calls[0].block_id).to_equal(0)
expect(result.advice_calls[0].instruction_index).to_equal(3)
```

</details>

#### builds assignment-only weaving rules that match MIR assignment join points

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = aop_log_weaving_config(AopLogInstrumentationConfig.for_debug(false, true))
val blocks = [MirBlockInfo(id: 1, instruction_kinds: [InstructionInfo(index: 4, kind_tag: "assignment")])]
val result = weave_function(config, "run", "app.debug", [], [], blocks)
expect(result.advices_inserted).to_equal(1)
expect(result.advice_calls[0].join_point_kind).to_equal(JoinPointKind.VariableAssignment)
expect(result.advice_calls[0].block_id).to_equal(1)
expect(result.advice_calls[0].instruction_index).to_equal(4)
```

</details>

#### wires global log rules before the no-advice skip

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = rt_file_read_text("src/compiler/80.driver/driver_pipeline.spl") ?? ""
val log_rules_idx = driver.find("val log_rules = aop_log_weaving_rules(log_config)")
val skip_idx = driver.find("no advice declarations or enabled log instrumentation found")
expect(log_rules_idx.?).to_equal(true)
expect(skip_idx.?).to_equal(true)
expect(skip_idx.unwrap() > log_rules_idx.unwrap()).to_equal(true)
expect(driver.contains("all_advices.len() == 0")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_log_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP Log Policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
