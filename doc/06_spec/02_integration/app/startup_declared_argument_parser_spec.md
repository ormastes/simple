# Startup Declared Argument Parser Specification

> Tests covering Startup declared-argument parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Declared Argument Parser Specification

## Scenarios

### Startup declared-argument parser

#### parses a declared argument and carries its value through

- Declare a single --config argument in the artifact schema
- Parse a command line that supplies it
- Confirm the parse succeeded and the supplied value survived
   - Expected: value_of(parsed, "--config") equals `prod.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Declare a single --config argument in the artifact schema")
val schema = schema_with_one_flag()

step("Parse a command line that supplies it")
val parsed = startup_parse_file_arguments("/app/entry.spl", ["--config", "prod.sdn"], schema)

step("Confirm the parse succeeded and the supplied value survived")
expect(parsed.ok).to_be(true)
expect(value_of(parsed, "--config")).to_equal("prod.sdn")
```

</details>

#### applies the declared default when the argument is absent

- Parse an empty command line against the same schema
- Confirm the schema default was applied rather than an empty value
   - Expected: value_of(parsed, "--config") equals `default.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse an empty command line against the same schema")
val parsed = startup_parse_file_arguments("/app/entry.spl", [], schema_with_one_flag())

step("Confirm the schema default was applied rather than an empty value")
expect(parsed.ok).to_be(true)
expect(value_of(parsed, "--config")).to_equal("default.sdn")
```

</details>

#### refuses to parse an argument the manifest never declared

- Parse a command line carrying an UNDECLARED --secret flag
- Confirm the undeclared name produced no parsed value
   - Expected: value_of(parsed, "--secret") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The discriminating case: a parser that accepts everything passes the two
# examples above and fails this one.
step("Parse a command line carrying an UNDECLARED --secret flag")
val parsed = startup_parse_file_arguments("/app/entry.spl", ["--secret", "hunter2"], schema_with_one_flag())

step("Confirm the undeclared name produced no parsed value")
expect(value_of(parsed, "--secret")).to_equal("")
```

</details>

#### reports an error rather than a silent empty when a required argument is missing

- Declare a REQUIRED argument with no default
- Parse a command line that omits it
- Confirm the parser failed closed and said why, instead of yielding an empty value


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Declare a REQUIRED argument with no default")
val schema = [ManifestArgument(
    name: "--input",
    value_kind: "text",
    required: true,
    default_value: ""
)]

step("Parse a command line that omits it")
val parsed = startup_parse_file_arguments("/app/entry.spl", [], schema)

step("Confirm the parser failed closed and said why, instead of yielding an empty value")
expect(parsed.ok).to_be(false)
expect(parsed.error.len()).to_be_greater_than(0)
```

</details>

#### keeps an empty schema from parsing anything at all

- Parse a populated command line against an EMPTY schema
- Confirm nothing was parsed — an empty schema is not a wildcard
   - Expected: parsed.values.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a populated command line against an EMPTY schema")
val empty_schema: [ManifestArgument] = []
val parsed = startup_parse_file_arguments("/app/entry.spl", ["--anything", "value"], empty_schema)

step("Confirm nothing was parsed — an empty schema is not a wildcard")
expect(parsed.values.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/startup_declared_argument_parser_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Startup declared-argument parser.
- Startup declared-argument parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
