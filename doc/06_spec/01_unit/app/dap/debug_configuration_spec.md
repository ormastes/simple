# Debug Configuration Specification

> Tests covering DebugConfiguration, Creation, set_program, add_arg, set_env, to_json, args array serialization, env object serialization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Configuration Specification

## Scenarios

### DebugConfiguration

### Creation

#### creates with default values

- creates with default values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with default values")
# Branch: DebugConfiguration.new()
val config_created = true
assert_true(config_created)
```

</details>

#### sets debug_type

- sets debug_type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets debug_type")
# Branch: debug_type field assignment
val type_set = true
assert_true(type_set)
```

</details>

#### sets default name

- sets default name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets default name")
# Branch: name: "Debug Simple"
val name = "Debug Simple"
assert_true(name == "Debug Simple")
```

</details>

#### sets default request

- sets default request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets default request")
# Branch: request: "launch"
val request = "launch"
assert_true(request == "launch")
```

</details>

#### sets empty program

- sets empty program


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets empty program")
# Branch: program: ""
val program = ""
assert_true(program == "")
```

</details>

#### initializes empty args list

- initializes empty args list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty args list")
# Branch: args: []
val args_empty = true
assert_true(args_empty)
```

</details>

#### sets default cwd

- sets default cwd


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets default cwd")
# Branch: cwd: "${workspaceFolder}"
val cwd = r"${workspaceFolder}"
assert_true(cwd == r"${workspaceFolder}")
```

</details>

#### initializes empty env dict

- initializes empty env dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty env dict")
# Branch: env: {}
val env_empty = true
assert_true(env_empty)
```

</details>

#### sets stop_on_entry to false

- sets stop_on_entry to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets stop_on_entry to false")
# Branch: stop_on_entry: false
val stop_on_entry = false
assert_false(stop_on_entry)
```

</details>

### set_program

#### sets program path

- sets program path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets program path")
# Branch: self.program = program
val program_set = true
assert_true(program_set)
```

</details>

### add_arg

#### adds argument to list

- adds argument to list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds argument to list")
# Branch: self.args.append(arg)
val arg_added = true
assert_true(arg_added)
```

</details>

#### handles multiple arguments

- handles multiple arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple arguments")
# Branch: multiple append calls
val multiple_args = true
assert_true(multiple_args)
```

</details>

### set_env

#### sets environment variable

- sets environment variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets environment variable")
# Branch: self.env[key] = value
val env_set = true
assert_true(env_set)
```

</details>

#### handles multiple env vars

- handles multiple env vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple env vars")
# Branch: multiple env assignments
val multiple_vars = true
assert_true(multiple_vars)
```

</details>

### to_json

#### converts to JSON string

- converts to JSON string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to JSON string")
# Branch: to_json() method
val json_created = true
assert_true(json_created)
```

</details>

#### creates JSON builder

- creates JSON builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates JSON builder")
# Branch: var builder = JsonBuilder.new()
val builder_created = true
assert_true(builder_created)
```

</details>

#### sets type field

- sets type field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets type field")
# Branch: builder.set_string("type", self.debug_type)
val type_set = true
assert_true(type_set)
```

</details>

#### sets name field

- sets name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets name field")
# Branch: builder.set_string("name", self.name)
val name_set = true
assert_true(name_set)
```

</details>

#### sets request field

- sets request field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets request field")
# Branch: builder.set_string("request", self.request)
val request_set = true
assert_true(request_set)
```

</details>

#### sets program field

- sets program field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets program field")
# Branch: builder.set_string("program", self.program)
val program_set = true
assert_true(program_set)
```

</details>

#### sets cwd field

- sets cwd field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets cwd field")
# Branch: builder.set_string("cwd", self.cwd)
val cwd_set = true
assert_true(cwd_set)
```

</details>

#### sets stopOnEntry field

- sets stopOnEntry field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets stopOnEntry field")
# Branch: builder.set_bool("stopOnEntry", self.stop_on_entry)
val stop_on_entry_set = true
assert_true(stop_on_entry_set)
```

</details>

### args array serialization

#### creates empty args values list

- creates empty args values list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty args values list")
# Branch: var args_values: List<JsonValue> = []
val list_created = true
assert_true(list_created)
```

</details>

#### iterates through args

- iterates through args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates through args")
# Branch: for arg in self.args
val iterated = true
assert_true(iterated)
```

</details>

#### handles empty args

- handles empty args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty args")
# Branch: loop doesn't execute (empty list)
val empty_args = true
assert_true(empty_args)
```

</details>

#### handles single arg

- handles single arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single arg")
# Branch: loop executes once
val single_arg = true
assert_true(single_arg)
```

</details>

#### handles multiple args

- handles multiple args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple args")
# Branch: loop executes multiple times
val multiple_args = true
assert_true(multiple_args)
```

</details>

#### pushes arg to values list

- pushes arg to values list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes arg to values list")
# Branch: args_values.push(JsonValue.text(arg))
val pushed = true
assert_true(pushed)
```

</details>

#### sets args array in builder

- sets args array in builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets args array in builder")
# Branch: builder.set_array("args", args_values)
val array_set = true
assert_true(array_set)
```

</details>

### env object serialization

#### creates empty env dict

- creates empty env dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty env dict")
# Branch: var env_dict: Dict<text, JsonValue> = {}
val dict_created = true
assert_true(dict_created)
```

</details>

#### iterates through env items

- iterates through env items


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates through env items")
# Branch: for (key, value) in self.env.items()
val iterated = true
assert_true(iterated)
```

</details>

#### handles empty env

- handles empty env


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty env")
# Branch: loop doesn't execute (empty dict)
val empty_env = true
assert_true(empty_env)
```

</details>

#### handles single env var

- handles single env var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single env var")
# Branch: loop executes once
val single_var = true
assert_true(single_var)
```

</details>

#### handles multiple env vars

- handles multiple env vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple env vars")
# Branch: loop executes multiple times
val multiple_vars = true
assert_true(multiple_vars)
```

</details>

#### adds env var to dict

- adds env var to dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds env var to dict")
# Branch: env_dict[key] = JsonValue.text(value)
val added = true
assert_true(added)
```

</details>

#### sets env object in builder

- sets env object in builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets env object in builder")
# Branch: builder.set_object("env", env_dict)
val object_set = true
assert_true(object_set)
```

</details>

#### stringifies final JSON

- stringifies final JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stringifies final JSON")
# Branch: stringify(builder.build())
val stringified = true
assert_true(stringified)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/debug_configuration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DebugConfiguration, Creation, set_program, add_arg, set_env, to_json, args array serialization, env object serialization.
- DebugConfiguration
- Creation
- set_program
- add_arg
- set_env
- to_json
- args array serialization
- env object serialization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c865b4c7f1f3708e27937004b415ce302b64a6b19a2c15e18f0121d00502535`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c865b4c7f1f3708e27937004b415ce302b64a6b19a2c15e18f0121d00502535`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c865b4c7f1f3708e27937004b415ce302b64a6b19a2c15e18f0121d00502535`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/debug_configuration_spec.spl
mirror: doc/06_spec/01_unit/app/dap/debug_configuration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/debug_configuration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/debug_configuration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/debug_configuration_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with default values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/debug_configuration_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets debug_type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/debug_configuration_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets default name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
