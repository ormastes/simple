# Context Generate Specification

> <details>

<!-- sdn-diagram:id=context_generate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_generate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_generate_spec -> app
context_generate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_generate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Generate Specification

## Scenarios

### simple context generator

#### renders markdown context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_context_fixture()
val output = context_generate(path, "hello", "markdown")
expect(output).to_contain("# Simple Context Pack")
expect(output).to_contain("target: `hello`")
expect(output).to_contain("fn hello")
```

</details>

#### renders json context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_context_fixture()
val output = context_generate(path, "hello", "json")
expect(output).to_contain("\"status\":\"ready\"")
expect(output).to_contain("\"target\":\"hello\"")
expect(output).to_contain("fn hello")
```

</details>

#### renders text context

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_context_fixture()
val output = context_generate(path, "hello", "text")
expect(output).to_start_with("Simple context pack")
expect(output).to_contain("status: ready")
```

</details>

#### renders stats

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_context_fixture()
val stats = context_stats(path, "hello")
expect(stats).to_contain("status: ready")
expect(stats).to_contain("lines:")
expect(stats).to_contain("token_estimate:")
```

</details>

#### estimates tokens by context character budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write_context_fixture()
val stats = context_stats(path, "hello")
expect(stats).to_contain("token_estimate: 10")
val output = context_index_packs([path], "hello", "text")
expect(output).to_contain("token_estimate: 10")
```

</details>

#### uses option-like missing output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val output = context_generate("build/test/does_not_exist.spl", "", "text")
expect(output).to_contain("status: missing")
expect(output).to_contain("content: none")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### keeps json output absence-marker-free

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val output = context_generate("build/test/does_not_exist.spl", "", "json")
expect(output).to_contain("\"status\":\"missing\"")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### reads quoted paths and heredoc-like content without shell expansion

- dir create all
- file write
   - Expected: output.split(absence_marker).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
dir_create_all("build/test/context quoted")
val path = "build/test/context quoted/o'clock.spl"
file_write(path, "fn marker() -> text:\n    \"SIMPLE_WRITE_EOF\"\n")
val output = context_generate(path, "marker", "text")
expect(output).to_contain("status: ready")
expect(output).to_contain("SIMPLE_WRITE_EOF")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### builds local pack index

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val path = _write_context_fixture()
val output = context_index_packs([path], "hello", "text")
expect(output).to_contain("Simple context index")
expect(output).to_contain("pack_count: 1")
expect(output).to_contain("source: " + path)
expect(output).to_contain("status: ready")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### queries local pack index

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val path = _write_context_fixture()
val index = context_index_packs([path], "hello", "text")
val output = context_query_index(index, "hello context", "text")
expect(output).to_contain("Simple context query")
expect(output).to_contain("status: ready")
expect(output).to_contain("matches:")
expect(output).to_contain("hello context")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### renders no-match query as explicit absence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val path = _write_context_fixture()
val index = context_index_packs([path], "hello", "text")
val output = context_query_index(index, "missing_symbol_name", "json")
expect(output).to_contain("\"status\":\"no_matches\"")
expect(output).to_contain("\"matches\":0")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### builds embedded sql pack index

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val path = _write_context_fixture()
val output = context_sql_index_packs([path], "hello", "", "text")
expect(output).to_contain("Simple context SQL index")
expect(output).to_contain("backend: sqlite")
if not output.contains("status: unavailable"):
    expect(output).to_contain("pack_count: 1")
    expect(output).to_contain("hello context")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### queries embedded sql pack index

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
val path = _write_context_fixture()
val output = context_sql_query_packs([path], "hello", "hello context", "", "json")
expect(output).to_contain("\"backend\":\"sqlite\"")
if not output.contains("\"status\":\"unavailable\""):
    expect(output).to_contain("\"status\":\"ready\"")
    expect(output).to_contain("\"matches\":")
    expect(output).to_contain("hello context")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### allows source-less embedded sql db queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
expect(context_args_allow_sourceless_sql_query(["--sql", "--query=hello", "--db=build/test/context.db"])).to_equal(true)
expect(context_args_allow_sourceless_sql_query(["--query=hello"])).to_equal(false)
expect(context_args_allow_sourceless_sql_query(["--sql", "--query="])).to_equal(false)

val output = context_sql_query_packs([], "", "hello", "", "text")
expect(output).to_contain("Simple context SQL query")
expect(output).to_contain("backend: sqlite")
if not output.contains("status: unavailable"):
    expect(output).to_contain("status: no_matches")
    expect(output).to_contain("matches: 0")
expect(output.split(absence_marker).len()).to_equal(1)
```

</details>

#### filters embedded sql query rows by source provenance

- dir create all
- file write
- file write
   - Expected: output.split(beta_path).len() equals `1`
   - Expected: output.split("beta_only").len() equals `1`
   - Expected: indexed.split(absence_marker).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absence_marker = "n" + "il"
dir_create_all("build/test")
val alpha_path = "build/test/context_alpha_source.spl"
val beta_path = "build/test/context_beta_source.spl"
val db_path = "build/test/context_source_filter.db"
file_write(alpha_path, "fn alpha_context() -> text:\n    \"shared_context_marker alpha_only\"\n")
file_write(beta_path, "fn beta_context() -> text:\n    \"shared_context_marker beta_only\"\n")

val indexed = context_sql_index_packs([alpha_path, beta_path], "ctx", db_path, "text")
expect(indexed).to_contain("backend: sqlite")
if not indexed.contains("status: unavailable"):
    val output = context_sql_query_packs_by_source([], "", "shared_context_marker", alpha_path, db_path, "text")
    expect(output).to_contain("Simple context SQL query")
    expect(output).to_contain("source_filter: " + alpha_path)
    expect(output).to_contain("matches: 1")
    expect(output).to_contain(alpha_path)
    expect(output).to_contain("alpha_only")
    expect(output.split(beta_path).len()).to_equal(1)
    expect(output.split("beta_only").len()).to_equal(1)
expect(indexed.split(absence_marker).len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/context_generate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple context generator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
