# Dict.get() Optional Wrapping Regression Tests

> Tests for Dict.get() return value handling. In the compiled runtime, Dict.get() auto-unwraps the optional, so .unwrap() fails with "method not found on type str".

<!-- sdn-diagram:id=dict_get_optional_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dict_get_optional_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dict_get_optional_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dict_get_optional_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict.get() Optional Wrapping Regression Tests

Tests for Dict.get() return value handling. In the compiled runtime, Dict.get() auto-unwraps the optional, so .unwrap() fails with "method not found on type str".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime \| Testing |
| Status | Confirmed (runtime limitation) |
| Source | `test/01_unit/compiler/config/dict_get_optional_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for Dict.get() return value handling. In the compiled runtime,
Dict.get() auto-unwraps the optional, so .unwrap() fails with
"method not found on type str".

Workaround: compare the result directly without .unwrap().

## Known Limitation

`dict.get("key").unwrap()` — FAILS (value already unwrapped)
`dict.get("key")` — WORKS (compare directly)
`dict.get("key").?` — WORKS (check presence)

## Scenarios

### Dict.get() Direct Comparison - Config

#### present key

#### returns value for existing key

1. var config = Config default
2. config set
   - Expected: config.get("key") equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("key", "value")
expect(config.get("key")).to_equal("value")
```

</details>

#### returns truthy for existing key check

1. var config = Config default
2. config set
   - Expected: config.get("key").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("key", "value")
expect(config.get("key").?).to_equal(true)
```

</details>

#### retrieves overwritten value

1. var config = Config default
2. config set
3. config set
   - Expected: config.get("key") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("key", "first")
config.set("key", "second")
expect(config.get("key")).to_equal("second")
```

</details>

#### retrieves multiple keys

1. var config = Config default
2. config set
3. config set
4. config set
   - Expected: config.get("a") equals `1`
   - Expected: config.get("b") equals `2`
   - Expected: config.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("a", "1")
config.set("b", "2")
config.set("c", "3")
expect(config.get("a")).to_equal("1")
expect(config.get("b")).to_equal("2")
expect(config.get("c")).to_equal("3")
```

</details>

#### missing key

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = Config.default()
expect(config.get("missing").?).to_equal(false)
```

</details>

#### is falsy for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = Config.default()
val result = config.get("nope")
expect(result.?).to_equal(false)
```

</details>

#### check-then-use pattern

#### checks presence then uses value

1. var config = Config default
2. config set
   - Expected: result equals `8080`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("port", "8080")
val result = config.get("port")
if result.?:
    expect(result).to_equal("8080")
else:
    fail("Config.get did not report present key after set")
```

</details>

#### handles missing in check pattern

1. fail
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = Config.default()
val result = config.get("missing")
if result.?:
    fail("Config.get reported missing key as present")
else:
    expect(result.?).to_equal(false)
```

</details>

#### multiple checks

1. var config = Config default
2. config set
3. config set
   - Expected: h.? is true
   - Expected: p.? is true
   - Expected: h equals `localhost`
   - Expected: p equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("host", "localhost")
config.set("port", "3000")
val h = config.get("host")
val p = config.get("port")
expect(h.?).to_equal(true)
expect(p.?).to_equal(true)
expect(h).to_equal("localhost")
expect(p).to_equal("3000")
```

</details>

### Dict.get() Direct Comparison - CompilerConfig

#### CLI args key=value

#### retrieves CLI-set value

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.get("output") equals `/tmp/out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--output=/tmp/out"])
expect(config.get("output")).to_equal("/tmp/out")
```

</details>

#### retrieves multiple CLI values

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.get("dir") equals `/build`
   - Expected: config.get("mode") equals `fast`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--dir=/build", "--mode=fast"])
expect(config.get("dir")).to_equal("/build")
expect(config.get("mode")).to_equal("fast")
```

</details>

#### returns nil for unset CLI key

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.get("nonexistent").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--deterministic"])
expect(config.get("nonexistent").?).to_equal(false)
```

</details>

#### SDN values

#### retrieves SDN-set value

1. var config = CompilerConfig default
2. config apply sdn
   - Expected: config.get("output") equals `dist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("output: dist")
expect(config.get("output")).to_equal("dist")
```

</details>

#### SDN value with spaces

1. var config = CompilerConfig default
2. config apply sdn
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("desc: a description")
val result = config.get("desc")
expect(result.?).to_equal(true)
```

</details>

#### CLI precedence over SDN

#### CLI value preserved over SDN

1. var config = CompilerConfig default
2. config apply cli args
3. config apply sdn
   - Expected: config.get("key") equals `from_cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--key=from_cli"])
config.apply_sdn("key: from_sdn")
expect(config.get("key")).to_equal("from_cli")
```

</details>

#### empty and special values

#### handles empty string value

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--empty="])
val result = config.get("empty")
# Note: empty string is falsy for .? operator
expect(result).to_equal("")
```

</details>

### Combined Dict + Enum Patterns

#### config with both dict and enum access

#### dict get + enum field method

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.profile.to_text() equals `prod`
3. config apply cli args
   - Expected: config.get("target") equals `x86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--profile", "prod"])
expect(config.profile.to_text()).to_equal("prod")
config.apply_cli_args(["--target=x86"])
expect(config.get("target")).to_equal("x86")
```

</details>

#### SDN then type inference enum

1. var config = CompilerConfig default
2. config apply sdn
   - Expected: config.get("backend") equals `cranelift`
   - Expected: config.type_inference.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("backend: cranelift")
expect(config.get("backend")).to_equal("cranelift")
expect(config.type_inference.empty_array_default.to_text()).to_equal("i32")
```

</details>

#### full config pipeline

1. var config = CompilerConfig default
2. config apply sdn
3. config apply cli args
   - Expected: config.get("opt_level") equals `2`
   - Expected: config.get("key") equals `val`
   - Expected: config.profile.to_text() equals `prod`
   - Expected: config.deterministic is true
   - Expected: config.type_inference.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("opt_level: 2")
config.apply_cli_args(["--profile", "prod", "--deterministic", "--key=val"])
expect(config.get("opt_level")).to_equal("2")
expect(config.get("key")).to_equal("val")
expect(config.profile.to_text()).to_equal("prod")
expect(config.deterministic).to_equal(true)
expect(config.type_inference.empty_array_default.to_text()).to_equal("i32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
