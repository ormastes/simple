# `simple check` diagnostic contract

> Exercises the real CLI path for diagnostics so stable error and warning codes,

<!-- sdn-diagram:id=check_diagnostics_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=check_diagnostics_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

check_diagnostics_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=check_diagnostics_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `simple check` diagnostic contract

Exercises the real CLI path for diagnostics so stable error and warning codes,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the real CLI path for diagnostics so stable error and warning codes,
help text, and summary status cannot be dropped between compiler diagnostics and
user-facing output.

## Scenarios

### `simple check` diagnostics

#### prints stable parse code and help in text output

1. seed invalid source
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_invalid_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", PARSE_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E0002]")
expect(combined).to_contain("unexpected token")
expect(combined).to_contain("expected: expression")
expect(combined).to_contain("found:    Dedent")
expect(combined).to_contain("= help: try adding `expression` before this token")
```

</details>

#### serializes stable parse code and help in JSON output

1. seed invalid source
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_invalid_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", "--json", PARSE_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("\"status\": \"error\"")
expect(combined).to_contain("\"code\": \"E0002\"")
expect(combined).to_contain("\"message\": \"unexpected token\"")
expect(combined).to_contain("\"expected\": \"expression\"")
expect(combined).to_contain("\"found\": \"Dedent\"")
expect(combined).to_contain("\"try adding `expression` before this token\"")
```

</details>

#### prints stable type mismatch code and help in text output

1. seed type mismatch source
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_type_mismatch_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", TYPE_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E1003]")
expect(combined).to_contain("type mismatch: expected i64, found text")
expect(combined).to_contain("expected: i64")
expect(combined).to_contain("found:    text")
expect(combined).to_contain("= help: change the annotation or use a value with the declared type")
```

</details>

#### serializes stable type mismatch code and help in JSON output

1. seed type mismatch source
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_type_mismatch_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", "--json", TYPE_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("\"status\": \"error\"")
expect(combined).to_contain("\"severity\": \"error\"")
expect(combined).to_contain("\"code\": \"E1003\"")
expect(combined).to_contain("\"message\": \"type mismatch: expected i64, found text\"")
expect(combined).to_contain("\"expected\": \"i64\"")
expect(combined).to_contain("\"found\": \"text\"")
expect(combined).to_contain("\"change the annotation or use a value with the declared type\"")
```

</details>

#### prints stable return type mismatch code and help in text output

1. seed return mismatch source
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_return_mismatch_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", RETURN_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E1003]")
expect(combined).to_contain("type mismatch: expected bool, found i64")
expect(combined).to_contain("expected: bool")
expect(combined).to_contain("found:    i64")
expect(combined).to_contain("= help: change the annotation or use a value with the declared type")
```

</details>

#### serializes stable return type mismatch code and help in JSON output

1. seed return mismatch source
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_return_mismatch_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", "--json", RETURN_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("\"status\": \"error\"")
expect(combined).to_contain("\"severity\": \"error\"")
expect(combined).to_contain("\"code\": \"E1003\"")
expect(combined).to_contain("\"message\": \"type mismatch: expected bool, found i64\"")
expect(combined).to_contain("\"expected\": \"bool\"")
expect(combined).to_contain("\"found\": \"i64\"")
expect(combined).to_contain("\"change the annotation or use a value with the declared type\"")
```

</details>

#### prints stable warning code and help in text output

1. seed unresolved import source
   - Expected: code equals `0`
   - Expected: combined does not contain `All checks passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_unresolved_import_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", WARNING_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(0)
expect(combined).to_contain("warning[W0410]")
expect(combined).to_contain("unresolved import 'definitely.missing.module'")
expect(combined).to_contain("= help: check the module path or add the source root with --source-root")
expect(combined).to_contain("1 warning(s) found in 1 file(s)")
expect(combined.contains("All checks passed")).to_equal(false)
```

</details>

#### serializes warning status and help in JSON output

1. seed unresolved import source
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
seed_unresolved_import_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", "--json", WARNING_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(0)
expect(combined).to_contain("\"status\": \"warning\"")
expect(combined).to_contain("\"severity\": \"warning\"")
expect(combined).to_contain("\"code\": \"W0410\"")
expect(combined).to_contain("\"unresolved import 'definitely.missing.module'")
expect(combined).to_contain("\"check the module path or add the source root with --source-root\"")
```

</details>

#### prints stable file read code and help in text output

1. remove missing fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
remove_missing_fixture()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", MISSING_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E0001]")
expect(combined).to_contain("cannot read file")
expect(combined).to_contain("= help: check that the path exists and is readable")
```

</details>

#### serializes stable file read code and help in JSON output

1. remove missing fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
remove_missing_fixture()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["check", "--json", MISSING_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("\"status\": \"error\"")
expect(combined).to_contain("\"severity\": \"error\"")
expect(combined).to_contain("\"code\": \"E0001\"")
expect(combined).to_contain("\"cannot read file")
expect(combined).to_contain("\"check that the path exists and is readable\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
