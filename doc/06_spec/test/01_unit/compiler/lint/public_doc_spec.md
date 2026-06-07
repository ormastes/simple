# Public Documentation Lint Specification

> PDOC002-005 use pdoc_extract_refs which calls pdoc_index_of internally.

<!-- sdn-diagram:id=public_doc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=public_doc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

public_doc_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=public_doc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Public Documentation Lint Specification

PDOC002-005 use pdoc_extract_refs which calls pdoc_index_of internally.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PDOC-001 through #PDOC-005 |
| Category | Tooling / Lint |
| Status | PDOC001 fully tested; PDOC002-005 implemented, require compiled mode |
| Requirements | doc/requirement/doc_ref_lint.md |
| Source | `test/01_unit/compiler/lint/public_doc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Interpreter Limitation

PDOC002-005 use pdoc_extract_refs which calls pdoc_index_of internally.
The interpreter has a bug where .find() returns an Option/enum type that
cannot be compared or used in arithmetic in nested scopes. pdoc_index_of
works around this but the ref extraction still fails when called from
inside while loops in the interpreter. These rules work in compiled mode.

## Scenarios

### PDOC001

#### warns on fn without sdoctest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn helper(x: i64) -> i64:\n    x + 1\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_be_greater_than(0)
```

</details>

#### no warning with sdoctest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "\"\"\"\nsdoctest:\n    expect(1).to_equal(1)\n\"\"\"\nfn square(x: i64) -> i64:\n    x * x\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### no warning with @sdoctest delegation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "\"\"\"\nsdoctest:\n    expect(foo(1)).to_equal(2)\n\"\"\"\nfn foo(x: i64) -> i64:\n    x * 2\n\n\"\"\"\n@sdoctest(foo)\n\"\"\"\nfn bar(x: i64) -> i64:\n    foo(x)\n"
val warnings = check_public_doc(source)
# bar has @sdoctest(foo), foo has sdoctest — neither should warn
# (foo has sdoctest, bar has @sdoctest)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### skips extern fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "extern fn rt_read(path: text) -> text\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### skips _private

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn _helper(x: i64) -> i64:\n    x + 1\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### skips marker function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn future_work(x: i64) -> i64:\n    " + "pass_" + "todo\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

#### warns on class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Parser:\n    input: text\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_be_greater_than(0)
```

</details>

#### handles empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_public_doc("")
expect(warnings.len()).to_equal(0)
```

</details>

#### struct and enum no PDOC001

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "struct Point:\n    x: i64\n\nenum Color:\n    Red\n"
val warnings = check_public_doc(source)
expect(count_by_code(warnings, "PDOC001")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/doc_ref_lint.md](doc/requirement/doc_ref_lint.md)


</details>
