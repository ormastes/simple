# CompilerConfig Specification

> Tests for CompilerConfig struct — default construction, CLI arg parsing, SDN application, key-value bag, and logger creation. Tests that require extern functions (env_get) are noted.

<!-- sdn-diagram:id=compiler_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_config_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CompilerConfig Specification

Tests for CompilerConfig struct — default construction, CLI arg parsing, SDN application, key-value bag, and logger creation. Tests that require extern functions (env_get) are noted.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/01_unit/compiler/config/compiler_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CompilerConfig struct — default construction, CLI arg parsing,
SDN application, key-value bag, and logger creation.
Tests that require extern functions (env_get) are noted.

## Scenarios

### Config

#### default

#### creates empty config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = Config.default()
val result = config.get("anything")
expect(result.?).to_equal(false)
```

</details>

#### get and set

#### stores and retrieves a value

1. var config = Config default
2. config set
   - Expected: result.? is true
   - Expected: result equals `value1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("key1", "value1")
val result = config.get("key1")
expect(result.?).to_equal(true)
expect(result).to_equal("value1")
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = Config.default()
val result = config.get("nonexistent")
expect(result.?).to_equal(false)
```

</details>

#### overwrites existing value

1. var config = Config default
2. config set
3. config set
   - Expected: result equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = Config.default()
config.set("key", "first")
config.set("key", "second")
val result = config.get("key")
expect(result).to_equal("second")
```

</details>

#### handles multiple keys

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

### CompilerConfig

#### default

#### has Dev profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.profile.to_text()).to_equal("dev")
```

</details>

#### has zero log level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.log_level).to_equal(0)
```

</details>

#### has use_rust_types false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.use_rust_types).to_equal(false)
```

</details>

#### has use_rust_interp false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.use_rust_interp).to_equal(false)
```

</details>

#### has use_rust_lexer false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.use_rust_lexer).to_equal(false)
```

</details>

#### has deterministic false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.deterministic).to_equal(false)
```

</details>

#### has coverage_enabled false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.coverage_enabled).to_equal(false)
```

</details>

#### has default type inference config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
expect(config.type_inference.empty_array_default.to_text()).to_equal("i32")
expect(config.type_inference.strict_empty_collections).to_equal(false)
```

</details>

#### get

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
val result = config.get("nonexistent")
expect(result.?).to_equal(false)
```

</details>

#### apply_cli_args

#### sets use_rust_types flag

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.use_rust_types is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--use-rust-types"])
expect(config.use_rust_types).to_equal(true)
```

</details>

#### sets fast_interp flag

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.use_rust_interp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--fast-interp"])
expect(config.use_rust_interp).to_equal(true)
```

</details>

#### sets fast_lex flag

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.use_rust_lexer is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--fast-lex"])
expect(config.use_rust_lexer).to_equal(true)
```

</details>

#### sets deterministic flag

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.deterministic is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--deterministic"])
expect(config.deterministic).to_equal(true)
```

</details>

#### sets coverage flag

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.coverage_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--coverage"])
expect(config.coverage_enabled).to_equal(true)
```

</details>

#### sets profile with next arg

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.profile.to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--profile", "prod"])
expect(config.profile.to_text()).to_equal("prod")
```

</details>

#### handles key=value form

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: result.? is true
   - Expected: result equals `/tmp/build`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--output-dir=/tmp/build"])
val result = config.get("output-dir")
expect(result.?).to_equal(true)
expect(result).to_equal("/tmp/build")
```

</details>

#### handles multiple flags

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.deterministic is true
   - Expected: config.coverage_enabled is true
   - Expected: config.use_rust_lexer is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--deterministic", "--coverage", "--fast-lex"])
expect(config.deterministic).to_equal(true)
expect(config.coverage_enabled).to_equal(true)
expect(config.use_rust_lexer).to_equal(true)
```

</details>

#### ignores unknown flags

1. var config = CompilerConfig default
2. config apply cli args
   - Expected: config.deterministic is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--unknown-flag"])
# Should not crash; config unchanged
expect(config.deterministic).to_equal(false)
```

</details>

#### apply_sdn

#### applies key-value pairs from SDN content

1. var config = CompilerConfig default
2. config apply sdn
   - Expected: config.get("output") equals `build`
   - Expected: config.get("optimize") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("output: build\noptimize: true")
expect(config.get("output")).to_equal("build")
expect(config.get("optimize")).to_equal("true")
```

</details>

#### skips comments

1. var config = CompilerConfig default
2. config apply sdn
   - Expected: config.get("key") equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("# comment\nkey: value")
expect(config.get("key")).to_equal("value")
```

</details>

#### skips empty lines

1. var config = CompilerConfig default
2. config apply sdn
   - Expected: config.get("key") equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_sdn("\n\nkey: value\n\n")
expect(config.get("key")).to_equal("value")
```

</details>

#### does not overwrite existing values

1. var config = CompilerConfig default
2. config apply cli args
3. config apply sdn
   - Expected: config.get("key") equals `cli_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.apply_cli_args(["--key=cli_value"])
config.apply_sdn("key: sdn_value")
# CLI takes precedence (already set before SDN)
expect(config.get("key")).to_equal("cli_value")
```

</details>

#### logger

#### creates logger with configured log level

1. var config = CompilerConfig default
   - Expected: log.level equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = CompilerConfig.default()
config.log_level = 10
val log = config.logger()
expect(log.level).to_equal(10)
```

</details>

#### creates silent logger by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CompilerConfig.default()
val log = config.logger()
expect(log.level).to_equal(0)
```

</details>

### Logger

#### construction

#### stores configured level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = Logger(level: 4)
expect(log.level).to_equal(4)
```

</details>

#### zero level is silent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = Logger(level: 0)
expect(log.level).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
