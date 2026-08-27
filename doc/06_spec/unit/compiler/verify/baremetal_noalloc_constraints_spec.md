# baremetal_noalloc_constraints_spec

> Bare-metal verifier noalloc source constraint regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# baremetal_noalloc_constraints_spec

Bare-metal verifier noalloc source constraint regression.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Bare-metal verifier noalloc source constraint regression.

This scans the verifier source so the production command continues to enforce
the same boundaries as the library dependency tests.

## Scenarios

### baremetal verifier noalloc constraints

#### has a reusable no-match source constraint helper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has a reusable no-match source constraint helper
   - Expected: _has("fn check_no_matches(label: text, cmd: text) -> bool:", path) is true
   - Expected: _has("matches.len() == 0", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has a reusable no-match source constraint helper")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("fn check_no_matches(label: text, cmd: text) -> bool:", path)).to_equal(true)
expect(_has("matches.len() == 0", path)).to_equal(true)
```

</details>

#### checks current build and documentation artifact paths

- checks current build and documentation artifact paths
   - Expected: _has("src/app/build/baremetal.smf", path) is true
   - Expected: _has("src/app/build/__init__.smf", path) is true
   - Expected: _has("src/app/build/types.smf", path) is true
   - Expected: _has("doc/07_guide/backend/baremetal.md", path) is true
   - Expected: _has("doc/09_report/2026/02/baremetal_build_system_integration_2026-02-14.md", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks current build and documentation artifact paths")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("src/app/build/baremetal.smf", path)).to_equal(true)
expect(_has("src/app/build/__init__.smf", path)).to_equal(true)
expect(_has("src/app/build/types.smf", path)).to_equal(true)
expect(_has("doc/07_guide/backend/baremetal.md", path)).to_equal(true)
expect(_has("doc/09_report/2026/02/baremetal_build_system_integration_2026-02-14.md", path)).to_equal(true)
```

</details>

#### guards noalloc against allocating runtime family imports

- guards noalloc against allocating runtime family imports
   - Expected: _has("no allocating-family imports from nogc_async_mut_noalloc", path) is true
   - Expected: _has("std\\\\.(nogc_sync_mut|nogc_async_mut|nogc_async_immut|gc_async_mut)\\\\.", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards noalloc against allocating runtime family imports")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no allocating-family imports from nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("std\\\\.(nogc_sync_mut|nogc_async_mut|nogc_async_immut|gc_async_mut)\\\\.", path)).to_equal(true)
```

</details>

#### guards noalloc against hosted app imports

- guards noalloc against hosted app imports
   - Expected: _has("no app imports from nogc_async_mut_noalloc", path) is true
   - Expected: _has("app\\\\.", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards noalloc against hosted app imports")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no app imports from nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("app\\\\.", path)).to_equal(true)
```

</details>

#### guards noalloc against allocation annotations

- guards noalloc against allocation annotations
   - Expected: _has("no allocation annotations in nogc_async_mut_noalloc", path) is true
   - Expected: _has("@alloc\\\\b", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards noalloc against allocation annotations")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no allocation annotations in nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("@alloc\\\\b", path)).to_equal(true)
```

</details>

#### guards noalloc against host allocation APIs

- guards noalloc against host allocation APIs
   - Expected: _has("no host allocation APIs in nogc_async_mut_noalloc", path) is true
   - Expected: _has("malloc|calloc|free", path) is true
   - Expected: _has("rt_alloc", path) is true
   - Expected: _has("extern fn .*realloc", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards noalloc against host allocation APIs")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no host allocation APIs in nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("malloc|calloc|free", path)).to_equal(true)
expect(_has("rt_alloc", path)).to_equal(true)
expect(_has("extern fn .*realloc", path)).to_equal(true)
```

</details>

#### guards noalloc against unsafe reachable helper imports

- guards noalloc against unsafe reachable helper imports
   - Expected: _has("no unsafe reachable imports from nogc_async_mut_noalloc", path) is true
   - Expected: _has("verify_noalloc_reachable_imports", path) is true
   - Expected: _has("compiler.tools.verify.noalloc_reachable", path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards noalloc against unsafe reachable helper imports")
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no unsafe reachable imports from nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("verify_noalloc_reachable_imports", path)).to_equal(true)
expect(_has("compiler.tools.verify.noalloc_reachable", path)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `0d874cc48ff5a8fe9709c8e198563394e334a5be1aa0e7f2264ec5943647d7a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d874cc48ff5a8fe9709c8e198563394e334a5be1aa0e7f2264ec5943647d7a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d874cc48ff5a8fe9709c8e198563394e334a5be1aa0e7f2264ec5943647d7a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl
mirror: doc/06_spec/unit/compiler/verify/baremetal_noalloc_constraints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verify/baremetal_noalloc_constraints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verify/baremetal_noalloc_constraints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a reusable no-match source constraint helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks current build and documentation artifact paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards noalloc against allocating runtime family imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
