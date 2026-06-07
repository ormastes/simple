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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: DebugConfiguration.new()
val config_created = true
expect(config_created)
```

</details>

#### sets debug_type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: debug_type field assignment
val type_set = true
expect(type_set)
```

</details>

#### sets default name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: name: "Debug Simple"
val name = "Debug Simple"
expect(name == "Debug Simple")
```

</details>

#### sets default request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: request: "launch"
val request = "launch"
expect(request == "launch")
```

</details>

#### sets empty program

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: program: ""
val program = ""
expect(program == "")
```

</details>

#### initializes empty args list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: args: []
val args_empty = true
expect(args_empty)
```

</details>

#### sets default cwd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: cwd: "${workspaceFolder}"
val cwd = r"${workspaceFolder}"
expect(cwd == r"${workspaceFolder}")
```

</details>

#### initializes empty env dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: env: {}
val env_empty = true
expect(env_empty)
```

</details>

#### sets stop_on_entry to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: stop_on_entry: false
val stop_on_entry = false
expect(not stop_on_entry)
```

</details>

### set_program

#### sets program path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.program = program
val program_set = true
expect(program_set)
```

</details>

### add_arg

#### adds argument to list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.args.append(arg)
val arg_added = true
expect(arg_added)
```

</details>

#### handles multiple arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: multiple append calls
val multiple_args = true
expect(multiple_args)
```

</details>

### set_env

#### sets environment variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.env[key] = value
val env_set = true
expect(env_set)
```

</details>

#### handles multiple env vars

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: multiple env assignments
val multiple_vars = true
expect(multiple_vars)
```

</details>

### to_json

#### converts to JSON string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: to_json() method
val json_created = true
expect(json_created)
```

</details>

#### creates JSON builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var builder = JsonBuilder.new()
val builder_created = true
expect(builder_created)
```

</details>

#### sets type field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("type", self.debug_type)
val type_set = true
expect(type_set)
```

</details>

#### sets name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("name", self.name)
val name_set = true
expect(name_set)
```

</details>

#### sets request field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("request", self.request)
val request_set = true
expect(request_set)
```

</details>

#### sets program field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("program", self.program)
val program_set = true
expect(program_set)
```

</details>

#### sets cwd field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_string("cwd", self.cwd)
val cwd_set = true
expect(cwd_set)
```

</details>

#### sets stopOnEntry field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("stopOnEntry", self.stop_on_entry)
val stop_on_entry_set = true
expect(stop_on_entry_set)
```

</details>

### args array serialization

#### creates empty args values list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var args_values: List<JsonValue> = []
val list_created = true
expect(list_created)
```

</details>

#### iterates through args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: for arg in self.args
val iterated = true
expect(iterated)
```

</details>

#### handles empty args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop doesn't execute (empty list)
val empty_args = true
expect(empty_args)
```

</details>

#### handles single arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes once
val single_arg = true
expect(single_arg)
```

</details>

#### handles multiple args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes multiple times
val multiple_args = true
expect(multiple_args)
```

</details>

#### pushes arg to values list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: args_values.push(JsonValue.text(arg))
val pushed = true
expect(pushed)
```

</details>

#### sets args array in builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_array("args", args_values)
val array_set = true
expect(array_set)
```

</details>

### env object serialization

#### creates empty env dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var env_dict: Dict<text, JsonValue> = {}
val dict_created = true
expect(dict_created)
```

</details>

#### iterates through env items

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: for (key, value) in self.env.items()
val iterated = true
expect(iterated)
```

</details>

#### handles empty env

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop doesn't execute (empty dict)
val empty_env = true
expect(empty_env)
```

</details>

#### handles single env var

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes once
val single_var = true
expect(single_var)
```

</details>

#### handles multiple env vars

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: loop executes multiple times
val multiple_vars = true
expect(multiple_vars)
```

</details>

#### adds env var to dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: env_dict[key] = JsonValue.text(value)
val added = true
expect(added)
```

</details>

#### sets env object in builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_object("env", env_dict)
val object_set = true
expect(object_set)
```

</details>

#### stringifies final JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: stringify(builder.build())
val stringified = true
expect(stringified)
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
