# mir_owns_its_name_strings_spec

> Purpose: Prove that MIR owns its function name strings (hazard 4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mir_owns_its_name_strings_spec

Purpose: Prove that MIR owns its function name strings (hazard 4).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that MIR owns its function name strings (hazard 4).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### MIR owns its function name strings (hazard 4)

#### has a live alias oracle, or reports every assertion as vacuous

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has a live alias oracle, or reports every assertion as vacuous
- Verify: has a live alias oracle, or reports every assertion as vacuous
   - Expected: live == true or live == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has a live alias oracle, or reports every assertion as vacuous")
step("Verify: has a live alias oracle, or reports every assertion as vacuous")
# @req: REQ-COMPILER-MIR-001
# Not an assertion about the compiler -- an assertion about the probe.
# Recorded so a future reader can tell a real GREEN from a dead oracle.
val live = oracle_is_live()
expect(live == true or live == false).to_equal(true)
```

</details>

#### detects a same-handle alias as verdict 0

- detects a same-handle alias as verdict 0
- Verify: detects a same-handle alias as verdict 0
   - Expected: distinct(shared, shared) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects a same-handle alias as verdict 0")
step("Verify: detects a same-handle alias as verdict 0")
if oracle_is_live():
    val shared = dyn_name(7)
    expect(distinct(shared, shared)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### RED: the pre-fix `= fn_.name` shape aliases the HIR string

- RED: the pre-fix `= fn_.name` shape aliases the HIR string
- Verify: RED: the pre-fix `= fn_.name` shape aliases the HIR string
   - Expected: distinct(h.name, m.name) equals `0`
   - Expected: distinct(h.export_name, m.export_name) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RED: the pre-fix `= fn_.name` shape aliases the HIR string")
step("Verify: RED: the pre-fix `= fn_.name` shape aliases the HIR string")
if oracle_is_live():
    val h = HirFnLike(name: dyn_name(9), export_name: dyn_name(10))
    val m = lower_aliasing(h)
    expect(distinct(h.name, m.name)).to_equal(0)  # oracle: 0 — named expected value from the requirement
    expect(distinct(h.export_name, m.export_name)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### GREEN: the landed `+ \

- GREEN: the landed `+ \
   - Expected: distinct(h.name, m.name) equals `1`
   - Expected: distinct(h.export_name, m.export_name) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("GREEN: the landed `+ \")
if oracle_is_live():
    val h = HirFnLike(name: dyn_name(11), export_name: dyn_name(12))
    val m = lower_owning(h)
    expect(distinct(h.name, m.name)).to_equal(1)  # oracle: 1 — named expected value from the requirement
    expect(distinct(h.export_name, m.export_name)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### pins WHY the copy idiom is `+ \

- pins WHY the copy idiom is `+ \
   - Expected: distinct(s, "{s}") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pins WHY the copy idiom is `+ \")
# Interpolating a whole string does NOT allocate a fresh one -- it
# returns the same handle. Anyone "simplifying" `s + ""` to "{s}"
# silently reintroduces hazard 4, so it is pinned here.
if oracle_is_live():
    val s = dyn_name(13)
    expect(distinct(s, "{s}")).to_equal(0)
```

</details>

#### confirms .replace() already gave method/static names a fresh string

- confirms .replace() already gave method/static names a fresh string
- Verify: confirms .replace() already gave method/static names a fresh string
   - Expected: distinct(s, s.replace("::", ".")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("confirms .replace() already gave method/static names a fresh string")
step("Verify: confirms .replace() already gave method/static names a fresh string")
# function_lowering.spl:139 uses `.replace("::", ".")`. That path was
# never part of hazard 4; this pins that it stays that way even when
# the pattern does not match.
if oracle_is_live():
    val s = dyn_name(15)
    expect(distinct(s, s.replace("::", "."))).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-MIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61ea5cef90afbbabb696cf958a7b605724110ae5810aadf9c5bae3689b42348e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61ea5cef90afbbabb696cf958a7b605724110ae5810aadf9c5bae3689b42348e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61ea5cef90afbbabb696cf958a7b605724110ae5810aadf9c5bae3689b42348e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_owns_its_name_strings_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_owns_its_name_strings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_owns_its_name_strings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a live alias oracle, or reports every assertion as vacuous' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a same-handle alias as verdict 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_owns_its_name_strings_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RED: the pre-fix `= fn_.name` shape aliases the HIR string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
