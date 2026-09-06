# Test Db Compiled Specification

> <details>

<!-- sdn-diagram:id=test_db_compiled_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_compiled_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_compiled_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_compiled_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Db Compiled Specification

## Scenarios

### compiled db local harness

#### roundtrips stable content without production imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = compiled_db_fixture()
val encoded = serialize_compiled_db(original)
val parsed = parse_compiled_db(encoded)

expect(parsed.interner.len()).to_equal(original.interner.len())
expect(parsed.files.len()).to_equal(1)
expect(parsed.suites.len()).to_equal(1)
expect(parsed.tests.len()).to_equal(1)
expect(parsed.tests[0].qualified_by).to_equal("")
expect(text_list_equals(parsed.interner.strings, original.interner.strings)).to_equal(true)
```

</details>

#### detects out-of-bounds references

1. var db = compiled db fixture
   - Expected: issues.len() > 0 is true
   - Expected: issues[0].severity equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = compiled_db_fixture()
db.tests.push(CompiledTestRecord(
    suite_id: 9,
    name_str: 99,
    category_str: 99,
    status_str: 99,
    qualified_by: ""
))

val issues = validate_interner_bounds(db)
expect(issues.len() > 0).to_equal(true)
expect(issues[0].severity).to_equal("error")
```

</details>

#### counts unqualified ignored tests

1. var db = compiled db fixture
2. name str: db interner intern
3. category str: db interner intern
4. name str: db interner intern
5. category str: db interner intern
   - Expected: count_unqualified_ignores(db, ignored) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = compiled_db_fixture()
val ignored = db.interner.intern("ignored")
db.tests.push(CompiledTestRecord(
    suite_id: 0,
    name_str: db.interner.intern("known_failure"),
    category_str: db.interner.intern("unit"),
    status_str: ignored,
    qualified_by: ""
))
db.tests.push(CompiledTestRecord(
    suite_id: 0,
    name_str: db.interner.intern("qualified_failure"),
    category_str: db.interner.intern("unit"),
    status_str: ignored,
    qualified_by: "issue-123"
))

expect(count_unqualified_ignores(db, ignored)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_db_compiled_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compiled db local harness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
