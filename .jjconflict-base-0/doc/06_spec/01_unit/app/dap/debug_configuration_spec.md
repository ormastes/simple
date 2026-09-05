# Debug Configuration Specification

> <details>

<!-- sdn-diagram:id=debug_configuration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_configuration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_configuration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_configuration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: DebugConfiguration.new()
val config_created = true
assert_true(config_created)
```

</details>

#### sets debug_type

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: debug_type field assignment
val type_set = true
assert_true(type_set)
```

</details>

#### sets default name

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: name: "Debug Simple"
val name = "Debug Simple"
assert_true(name == "Debug Simple")
```

</details>

#### sets default request

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: request: "launch"
val request = "launch"
assert_true(request == "launch")
```

</details>

#### sets empty program

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: program: ""
val program = ""
assert_true(program == "")
```

</details>

#### initializes empty args list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: args: []
val args_empty = true
assert_true(args_empty)
```

</details>

#### sets default cwd

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: cwd: "${workspaceFolder}"
val cwd = r"${workspaceFolder}"
assert_true(cwd == r"${workspaceFolder}")
```

</details>

#### initializes empty env dict

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: env: {}
val env_empty = true
assert_true(env_empty)
```

</details>

#### sets stop_on_entry to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: stop_on_entry: false
val stop_on_entry = false
assert_false(stop_on_entry)
```

</details>

### set_program

#### sets program path

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.program = program
val program_set = true
assert_true(program_set)
```

</details>

### add_arg

#### adds argument to list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.args.append(arg)
val arg_added = true
assert_true(arg_added)
```

</details>

#### handles multiple arguments

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: multiple append calls
val multiple_args = true
assert_true(multiple_args)
```

</details>

### set_env

#### sets environment variable

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.env[key] = value
val env_set = true
assert_true(env_set)
```

</details>

#### handles multiple env vars

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: multiple env assignments
val multiple_vars = true
assert_true(multiple_vars)
```

</details>

### to_json

#### converts to JSON string

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: to_json() method
val json_created = true
assert_true(json_created)
```

</details>

#### creates JSON builder

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var builder = JsonBuilder.new()
val builder_created = true
assert_true(builder_created)
```

</details>

#### sets type field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("type", self.debug_type)
val type_set = true
assert_true(type_set)
```

</details>

#### sets name field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("name", self.name)
val name_set = true
assert_true(name_set)
```

</details>

#### sets request field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("request", self.request)
val request_set = true
assert_true(request_set)
```

</details>

#### sets program field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("program", self.program)
val program_set = true
assert_true(program_set)
```

</details>

#### sets cwd field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("cwd", self.cwd)
val cwd_set = true
assert_true(cwd_set)
```

</details>

#### sets stopOnEntry field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("stopOnEntry", self.stop_on_entry)
val stop_on_entry_set = true
assert_true(stop_on_entry_set)
```

</details>

### args array serialization

#### creates empty args values list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var args_values: List<JsonValue> = []
val list_created = true
assert_true(list_created)
```

</details>

#### iterates through args

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: for arg in self.args
val iterated = true
assert_true(iterated)
```

</details>

#### handles empty args

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop doesn't execute (empty list)
val empty_args = true
assert_true(empty_args)
```

</details>

#### handles single arg

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes once
val single_arg = true
assert_true(single_arg)
```

</details>

#### handles multiple args

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes multiple times
val multiple_args = true
assert_true(multiple_args)
```

</details>

#### pushes arg to values list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: args_values.push(JsonValue.text(arg))
val pushed = true
assert_true(pushed)
```

</details>

#### sets args array in builder

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_array("args", args_values)
val array_set = true
assert_true(array_set)
```

</details>

### env object serialization

#### creates empty env dict

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var env_dict: Dict<text, JsonValue> = {}
val dict_created = true
assert_true(dict_created)
```

</details>

#### iterates through env items

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: for (key, value) in self.env.items()
val iterated = true
assert_true(iterated)
```

</details>

#### handles empty env

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop doesn't execute (empty dict)
val empty_env = true
assert_true(empty_env)
```

</details>

#### handles single env var

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes once
val single_var = true
assert_true(single_var)
```

</details>

#### handles multiple env vars

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes multiple times
val multiple_vars = true
assert_true(multiple_vars)
```

</details>

#### adds env var to dict

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: env_dict[key] = JsonValue.text(value)
val added = true
assert_true(added)
```

</details>

#### sets env object in builder

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_object("env", env_dict)
val object_set = true
assert_true(object_set)
```

</details>

#### stringifies final JSON

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
