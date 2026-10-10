# Spec Facade Owner Specification

> Tests covering Canonical spec facade execution ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Facade Owner Specification

## Scenarios

### Canonical spec facade execution ownership

#### enumerates three stable cases without body side effects

- Resolve the configured native owner fixture
   - Expected: file_exists(ledger) is false
- Enumerate real registrations without invoking callbacks
   - Expected: env_get("SIMPLE_RUNTIME_MODE") equals `outer_mode`
   - Expected: result[2] equals `0`
   - Expected: result[0] does not contain `FACADE_BODY_`
   - Expected: result[0] does not contain `FACADE_FORBIDDEN_BODY`
   - Expected: facade_rows(captured, "declare\t").len() equals `3`
   - Expected: facade_rows(captured, "result\t").len() equals `0`
   - Expected: captured contains `test_callbacks_executed=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the configured native owner fixture")
val binary = env_get("SIMPLE_SPEC_FACADE_NATIVE_BINARY")
val dir = env_get("SIMPLE_SPEC_FACADE_EVIDENCE_DIR")
expect(binary.len()).to_be_greater_than(0)
expect(dir.len()).to_be_greater_than(0)
val ledger = dir + "/enumerate.registry.tsv"
expect(file_exists(ledger)).to_equal(false)
val outer_mode = env_get("SIMPLE_RUNTIME_MODE")
step("Enumerate real registrations without invoking callbacks")
val result = process_run(binary, ["--enumerate", "--registry-output=" + ledger])
expect(env_get("SIMPLE_RUNTIME_MODE")).to_equal(outer_mode)
expect(result[2]).to_equal(0)
expect(result[0].contains("FACADE_BODY_")).to_equal(false)
expect(result[0].contains("FACADE_FORBIDDEN_BODY")).to_equal(false)
val captured = file_read(ledger)
expect(facade_rows(captured, "declare\t").len()).to_equal(3)
expect(facade_rows(captured, "result\t").len()).to_equal(0)
expect(captured.contains("test_callbacks_executed=0")).to_equal(true)
```

</details>

#### propagates failed checks and executes compiled-only callbacks in native mode

- Execute the same native registrations
   - Expected: file_exists(ledger) is false
   - Expected: file_exists(baseline) is false
   - Expected: env_get("SIMPLE_RUNTIME_MODE") equals `outer_mode`
   - Expected: enumerated[2] equals `0`
   - Expected: enumerated[0] does not contain `FACADE_BODY_`
   - Expected: enumerated[0] does not contain `FACADE_FORBIDDEN_BODY`
   - Expected: facade_rows(file_read(baseline), "declare\t").len() equals `3`
   - Expected: env_get("SIMPLE_RUNTIME_MODE") equals `outer_mode`
   - Expected: result[2] equals `1`
   - Expected: result[0] contains `FACADE_BODY_PASS`
   - Expected: result[0] contains `FACADE_BODY_FAIL`
   - Expected: result[0] contains `FACADE_FORBIDDEN_BODY`
- Join exact registry identities and actual failure receipts
   - Expected: results.len() equals `3`
   - Expected: passed equals `1`
   - Expected: failed equals `2`
   - Expected: facade_rows(captured, "declare\t") equals `facade_rows(file_read(baseline), "declare\t")`
   - Expected: captured contains `test_callbacks_executed=3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the same native registrations")
val binary = env_get("SIMPLE_SPEC_FACADE_NATIVE_BINARY")
val dir = env_get("SIMPLE_SPEC_FACADE_EVIDENCE_DIR")
val ledger = dir + "/run.registry.tsv"
expect(file_exists(ledger)).to_equal(false)
val outer_mode = env_get("SIMPLE_RUNTIME_MODE")
val baseline = dir + "/run-baseline.registry.tsv"
expect(file_exists(baseline)).to_equal(false)
val enumerated = process_run(binary, ["--enumerate", "--registry-output=" + baseline])
expect(env_get("SIMPLE_RUNTIME_MODE")).to_equal(outer_mode)
expect(enumerated[2]).to_equal(0)
expect(enumerated[0].contains("FACADE_BODY_")).to_equal(false)
expect(enumerated[0].contains("FACADE_FORBIDDEN_BODY")).to_equal(false)
expect(facade_rows(file_read(baseline), "declare\t").len()).to_equal(3)
val result = process_run(binary, ["--run", "--registry-output=" + ledger])
expect(env_get("SIMPLE_RUNTIME_MODE")).to_equal(outer_mode)
expect(result[2]).to_equal(1)
expect(result[0].contains("FACADE_BODY_PASS")).to_equal(true)
expect(result[0].contains("FACADE_BODY_FAIL")).to_equal(true)
expect(result[0].contains("FACADE_FORBIDDEN_BODY")).to_equal(true)
step("Join exact registry identities and actual failure receipts")
val captured = file_read(ledger)
val results = facade_rows(captured, "result\t")
var passed = 0
var failed = 0
for row in results:
    if row.ends_with("\tpass"): passed = passed + 1
    if row.ends_with("\tfail"): failed = failed + 1
expect(results.len()).to_equal(3)
expect(passed).to_equal(1)
expect(failed).to_equal(2)
expect(facade_rows(captured, "declare\t")).to_equal(facade_rows(file_read(baseline), "declare\t"))
expect(captured.contains("test_callbacks_executed=3")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `C:\dev\simple\build\spec-facade-owner-repair-20261010\candidate\test\02_integration\lib\spec_facade_owner_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Canonical spec facade execution ownership.
- Canonical spec facade execution ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
