# X25519mlkem768 Manifest Existence Gate Specification

> Tests covering X25519MLKEM768 campaign manifest existence gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Manifest Existence Gate Specification

## Scenarios

### X25519MLKEM768 campaign manifest existence gate

#### should prove the checker can go RED on a path that is not on disk

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phantom = "src/app/test/no_such_manifest_entry_exists.spl"
val absent = x25519_mlkem768_coverage_absent_in([phantom])
assert_equal(absent.len(), 1)
assert_equal(absent[0], phantom)
```

</details>

#### should not report a path that does exist

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absent = x25519_mlkem768_coverage_absent_in(
    ["src/app/test/x25519mlkem768_coverage_contract.spl"])
assert_equal(absent.len(), 0)
```

</details>

#### should list every declared coverage-contract path exactly once

- assert equal
- assert false
- seen push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = x25519_mlkem768_coverage_manifest_paths()
assert_equal(paths.len(), 37)
var seen: [text] = []
for path in paths:
    assert_false(seen.contains(path))
    seen.push(path)
```

</details>

#### should list every declared critical-inventory path exactly once

- assert equal
- assert false
- seen push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = critical_manifest_paths()
assert_equal(paths.len(), 24)
var seen: [text] = []
for path in paths:
    assert_false(seen.contains(path))
    seen.push(path)
```

</details>

#### should find no unexpectedly absent path in the coverage contract

- print x25519 mlkem768 coverage manifest gate report
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absent = x25519_mlkem768_coverage_manifest_absent_paths()
print x25519_mlkem768_coverage_manifest_gate_report()
assert_equal(absent.join(","), "")
```

</details>

#### should find no unexpectedly absent path in the critical inventory

- print "critical-inventory manifest-existence-gate: absent={absent len
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absent = x25519_mlkem768_coverage_absent_in(critical_manifest_paths())
print "critical-inventory manifest-existence-gate: absent={absent.len()}"
assert_equal(absent.join(","), "")
```

</details>

#### should retire a declared block once the module lands

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stale = x25519_mlkem768_coverage_stale_blocked_paths()
assert_equal(stale.join(","), "")
```

</details>

#### should keep every declared-blocked path named inside a manifest

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for path in x25519_mlkem768_coverage_declared_blocked_paths():
    assert_true(x25519_mlkem768_coverage_manifest_paths().contains(path))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_manifest_existence_gate_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 campaign manifest existence gate.
- X25519MLKEM768 campaign manifest existence gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
