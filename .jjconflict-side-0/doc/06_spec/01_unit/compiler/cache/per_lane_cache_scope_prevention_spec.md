# Per-Lane Cache Scope — Prevention

> The reproducing spec (`per_lane_cache_scope_spec.spl`) proves the one case that

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Lane Cache Scope — Prevention

The reproducing spec (`per_lane_cache_scope_spec.spl`) proves the one case that

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Design | doc/05_design/compiler/incremental_build/per_lane_private_caches.md |
| Source | `test/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reproducing spec (`per_lane_cache_scope_spec.spl`) proves the one case that
motivated the work: two lanes over one cache directory. This spec probes the
ADJACENT cases where the same defect class would reappear, and the fail-closed
properties that keep the guard from degrading into a rubber stamp.

The failure mode being prevented is specific: a cache guard that keeps returning
PASS is indistinguishable from no guard at all. So every case below asserts a
NON-pass outcome where one is required, and the guard's own fixture selftest is
run as a case in its own right.

## Scope and Preconditions

Subprocess-only; no compiler and no build.

## Key Concepts

| Concept | Description |
|---------|-------------|
| fail-closed | Nothing checked is ERROR (exit 2), never a pass |
| unset default | An undeclared lane resolves to `default`, preserving single-lane behaviour |

## Scenarios

### Per-lane cache scope prevention

#### passes its own fixture selftest before it is trusted to gate anything

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes its own fixture selftest before it is trusted to gate anything
- Run the guard's built-in fixtures
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes its own fixture selftest before it is trusted to gate anything")
step("Run the guard's built-in fixtures")
val (out, code) = run_args([guard, "--selftest"])
expect(out).to_contain("PASS")
expect(out).to_contain("fixture")
expect(code).to_equal(0)
```

</details>

#### reports ERROR rather than PASS when it was given nothing to check

- reports ERROR rather than PASS when it was given nothing to check
- Invoke the guard with no cache directory and no lane
- A run that checked nothing must never look like a clean run
   - Expected: code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports ERROR rather than PASS when it was given nothing to check")
step("Invoke the guard with no cache directory and no lane")
val (out, code) = run_args([guard])
step("A run that checked nothing must never look like a clean run")
expect(out).to_contain("ERROR")
expect(code).to_equal(2)
```

</details>

#### refuses a cache whose ownership marker is unreadable

- refuses a cache whose ownership marker is unreadable
- A cache directory carries an empty, corrupt ownership marker
- A lane asks to reuse it
- Unknown ownership is treated as foreign, not as unowned
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses a cache whose ownership marker is unreadable")
step("A cache directory carries an empty, corrupt ownership marker")
val dir = scratch("corrupt")
file_write(dir + "/.cache_scope", "")

step("A lane asks to reuse it")
val (out, code) = run_args([guard, dir, "stage2"])

step("Unknown ownership is treated as foreign, not as unowned")
expect(out).to_contain("FAIL")
expect(code).to_equal(1)
```

</details>

#### keeps the unset-scope default usable as an ordinary single-lane cache

- keeps the unset-scope default usable as an ordinary single-lane cache
- A build that never declared a lane uses the documented `default` scope
   - Expected: first_code equals `0`
- Repeated single-lane builds keep reusing it, as before the change
   - Expected: second_code equals `0`
- But a declared lane still cannot borrow the default lane's cache
   - Expected: third_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the unset-scope default usable as an ordinary single-lane cache")
step("A build that never declared a lane uses the documented `default` scope")
val dir = scratch("unset_default")
val (first, first_code) = run_args([guard, dir, "default"])
expect(first).to_contain("PASS")
expect(first_code).to_equal(0)

step("Repeated single-lane builds keep reusing it, as before the change")
val (second, second_code) = run_args([guard, dir, "default"])
expect(second).to_contain("PASS")
expect(second_code).to_equal(0)

step("But a declared lane still cannot borrow the default lane's cache")
val (third, third_code) = run_args([guard, dir, "stage4"])
expect(third).to_contain("FAIL")
expect(third).to_contain("default")
expect(third_code).to_equal(1)
```

</details>

#### separates two lanes that share one compiler binary

- separates two lanes that share one compiler binary
- Phase-4 tool builds and the census lane run the SAME compiler
   - Expected: a_code equals `0`
   - Expected: b_code equals `0`
- Identical compiler identity is NOT enough to share a cache
   - Expected: cross_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("separates two lanes that share one compiler binary")
step("Phase-4 tool builds and the census lane run the SAME compiler")
val tools = scratch("tools")
val census = scratch("census")
val (a, a_code) = run_args([guard, tools, "stage4-tools"])
val (b, b_code) = run_args([guard, census, "stage4-census"])
expect(a_code).to_equal(0)
expect(b_code).to_equal(0)

step("Identical compiler identity is NOT enough to share a cache")
val (cross, cross_code) = run_args([guard, tools, "stage4-census"])
expect(cross).to_contain("FAIL")
expect(cross_code).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6ffc76b16d607dfac87fcafdca6ae191cb041233add69b555fa76375fec2625b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ffc76b16d607dfac87fcafdca6ae191cb041233add69b555fa76375fec2625b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ffc76b16d607dfac87fcafdca6ae191cb041233add69b555fa76375fec2625b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes its own fixture selftest before it is trusted to gate anything' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports ERROR rather than PASS when it was given nothing to check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/per_lane_cache_scope_prevention_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a cache whose ownership marker is unreadable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
