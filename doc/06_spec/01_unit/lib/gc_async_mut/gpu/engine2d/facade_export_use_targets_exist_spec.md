# Facade Export Use Targets Exist Specification

> Tests covering no gc_async_mut engine2d facade re-exports a module that does not exist.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facade Export Use Targets Exist Specification

## Scenarios

### no gc_async_mut engine2d facade re-exports a module that does not exist

#### self-check of the resolver (guards against a vacuous green)

#### resolves a module that is known to exist

- resolves a module that is known to exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a module that is known to exist")
assert_true(module_resolves("std.nogc_sync_mut.gpu.engine2d.sffi_cuda"))
```

</details>

#### rejects a module that is known NOT to exist

- rejects a module that is known NOT to exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a module that is known NOT to exist")
assert_true(not module_resolves("std.nogc_async_mut.gpu.engine2d.ffi_cuda"))
```

</details>

#### parses an export-use line into its dotted target

- parses an export-use line into its dotted target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses an export-use line into its dotted target")
assert_equal(
    export_use_target("export use std.a.b.c.*"),
    "std.a.b.c")
```

</details>

#### every facade in the engine2d directory

#### has zero dangling export-use targets

- has zero dangling export-use targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has zero dangling export-use targets")
var dangling: [str] = []
var scanned = 0
for name in dir_list(FACADE_DIR):
    if name.ends_with(".spl"):
        scanned = scanned + 1
        for bad in dangling_targets_in(FACADE_DIR + name):
            dangling.push(bad)
# non-vacuity: an empty scan must never read as a pass
assert_true(scanned > 0)
if dangling.len() > 0:
    print("dangling export-use targets:")
    for d in dangling:
        print("  " + d)
assert_equal(dangling.len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no gc_async_mut engine2d facade re-exports a module that does not exist.
- no gc_async_mut engine2d facade re-exports a module that does not exist

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b79c346b64abcd440e8f9511fa4fe3ed0c43e1a31313bc9b97ea58641e44ba77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b79c346b64abcd440e8f9511fa4fe3ed0c43e1a31313bc9b97ea58641e44ba77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b79c346b64abcd440e8f9511fa4fe3ed0c43e1a31313bc9b97ea58641e44ba77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a module that is known to exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a module that is known NOT to exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/facade_export_use_targets_exist_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses an export-use line into its dotted target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
