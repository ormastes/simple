# Argument Parsing Specification

> Command-line argument parsing utilities for global flags, internal flags,

<!-- sdn-diagram:id=arg_parsing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arg_parsing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arg_parsing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arg_parsing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argument Parsing Specification

Command-line argument parsing utilities for global flags, internal flags,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3120 |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/arg_parsing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Command-line argument parsing utilities for global flags, internal flags,
and language configuration. Provides structured parsing of CLI arguments
with support for flag values and option filtering.

*Migrated from: src/driver/src/cli/commands/arg_parsing.rs*

NOTE: This spec uses a local parser harness so it can exercise the expected
behavior without calling unsupported static methods from the bootstrap runtime.

## Scenarios

### GlobalFlags parsing

#### parses gc_log and debug_mode flags

#### sets gc_log to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--gc-log"])
expect(flags.gc_log).to_equal(true)
expect(flags.gc_off).to_equal(false)
```

</details>

#### sets debug_mode to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--debug"])
expect(flags.debug_mode).to_equal(true)
expect(flags.gc_log).to_equal(false)
```

</details>

#### keeps gc_off false when unrelated flags are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--notui"])
expect(flags.gc_off).to_equal(false)
```

</details>

#### parses gc_off flag

#### recognizes lowercase --gc=off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--gc=off"])
expect(flags.gc_off).to_equal(true)
```

</details>

#### recognizes uppercase --gc=OFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--gc=OFF"])
expect(flags.gc_off).to_equal(true)
```

</details>

#### parses other flags

#### sets macro_trace to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--macro-trace"])
expect(flags.macro_trace).to_equal(true)
```

</details>

#### sets use_notui to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_global_flags(["--notui"])
expect(flags.use_notui).to_equal(true)
```

</details>

#### parses fixed backend flags

#### defaults --fixed-be to llvm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_fixed_backend(["--fixed-be"])
expect(flags.backend).to_equal("llvm")
```

</details>

#### keeps an explicit fixed backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_fixed_backend(["--fixed-be=llvm-lib"])
expect(flags.backend).to_equal("llvm-lib")
```

</details>

#### normalizes an empty fixed backend value to llvm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_fixed_backend(["--fixed-be="])
expect(flags.backend).to_equal("llvm")
```

</details>

#### lets fixed-be override an earlier backend flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_fixed_backend(["--backend=cranelift", "--fixed-be"])
expect(flags.backend).to_equal("llvm")
```

</details>

### filter_internal_flags

#### removes single flags

#### keeps only user arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "run", "--gc-log", "--debug", "test/example.spl"]
val filtered = filter_internal_flags(args)
expect(filtered.len()).to_equal(3)
expect(filtered[0]).to_equal("simple")
expect(filtered[1]).to_equal("run")
expect(filtered[2]).to_equal("test/example.spl")
```

</details>

#### removes flags with values

#### removes both flag and value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "--time-limit", "120", "--lang", "ko", "test/example.spl"]
val filtered = filter_internal_flags(args)
expect(filtered.len()).to_equal(2)
expect(filtered[0]).to_equal("simple")
expect(filtered[1]).to_equal("test/example.spl")
```

</details>

#### handles mixed flags

#### filters correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "--sandbox", "--read-only", "fixtures", "run", "--no-network", "test/example.spl", "--gc=off"]
val filtered = filter_internal_flags(args)
expect(filtered.len()).to_equal(3)
expect(filtered[0]).to_equal("simple")
expect(filtered[1]).to_equal("run")
expect(filtered[2]).to_equal("test/example.spl")
```

</details>

### parse_lang_flag

#### sets environment variable

#### extracts the lang value safely

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang = parse_lang_flag_value(["simple", "--lang", "ko", "run"])
expect(lang.?).to_equal(true)
expect(lang? == "ko")
```

</details>

#### returns nil when lang flag is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang = parse_lang_flag_value(["simple", "run"])
expect(lang.?).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
