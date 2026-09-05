# Sql Facade Specification

> Tests covering gc_async_mut database SQL facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Facade Specification

## Scenarios

### gc_async_mut database SQL facades

#### re-exports pure SQL helper submodules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports pure SQL helper submodules
   - Expected: quote_ident("users") equals `"users"`
   - Expected: placeholder_list(3) equals `?, ?, ?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports pure SQL helper submodules")
expect(quote_ident("users")).to_equal("\"users\"")
expect(placeholder_list(3)).to_equal("?, ?, ?")
```

</details>

#### re-exports query builder and value types

- re-exports query builder and value types
   - Expected: built.1.len() equals `1`
   - Expected: expr.params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports query builder and value types")
var query = SelectQuery.from("users")
query = query.where_eq("id", DbValue.Integer(value: 7))
query = query.order("name", SqlOrder.Asc)
val built = query.build()
val expr = compile_expr(sql_eq("name", DbValue.Text(value: "Ada")))

expect(built.0).to_contain("WHERE")
expect(built.1.len()).to_equal(1)
expect(expr.params.len()).to_equal(1)
```

</details>

#### re-exports schema builders

- re-exports schema builders
   - Expected: schema.columns.len() equals `1`
   - Expected: value.db_type() equals `DbType.Integer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports schema builders")
var schema = TableSchema.new("users")
schema = schema.col(ColumnDef.integer("id").pk())
val value = DbValue.Integer(value: 1)

expect(schema.columns.len()).to_equal(1)
expect(value.db_type()).to_equal(DbType.Integer)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut database SQL facades.
- gc_async_mut database SQL facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96c14e3513796b8f24e5c39f62fd4142dd95f1a9838052f675b984ab4a193183`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96c14e3513796b8f24e5c39f62fd4142dd95f1a9838052f675b984ab4a193183`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96c14e3513796b8f24e5c39f62fd4142dd95f1a9838052f675b984ab4a193183`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pure SQL helper submodules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports query builder and value types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports schema builders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
