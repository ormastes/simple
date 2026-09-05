# `unsafe(capabilities: [...]):` block form reaches the Any-escape checker

> Reproduce specs for two bug records that were one gap seen from two sides:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `unsafe(capabilities: [...]):` block form reaches the Any-escape checker

Reproduce specs for two bug records that were one gap seen from two sides:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | In Progress |
| Research | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md §8.1 |
| Source | `test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Reproduce specs for two bug records that were one gap seen from two sides:

- doc/08_tracking/bug/unsafe_capability_block_syntax_not_parsed_2026-08-21.md —
  `unsafe(reason: ..., capabilities: [...]):` did not parse as an unsafe block.
- doc/08_tracking/bug/unsafe_capabilities_not_carried_into_hir_2026-08-21.md —
  the capability names never reached HIR, so `any_escape` had to take the grant
  as a profile input.

Every scenario passes an EMPTY grant list: the only way a region can be granted
here is through the capability names lowered onto `HirBlock.unsafe_caps`.

## Scope and Preconditions

Each scenario lowers a fixture under `test/fixtures/any_escape/` to HIR and
runs `any_escape_check`. Pre-fix, the block form lowered to a plain expression
statement and every `Any` inside it was reported as an origin.

## Primary Workflow

Block form with `type_erasure` -> HIR `UnsafeBlock` whose body carries the
capability -> checker treats the region as granted.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `HirBlock.unsafe_caps` | Capability names carried on the body of `HirExprKind.UnsafeBlock` |
| `type_erasure` | The only capability that licenses `Any` inside the region |

## Related Specifications

- test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl (annotation form)

## Evidence and Provenance

The `raw_ptr`-only and unknown-capability neighbours are load-bearing: a fix
that treated ANY capability list as a grant would pass the primary scenario
and fail them.

## Recovery and Troubleshooting

A parse failure here means the statement-position `unsafe(` branch in
`parser_stmts.spl` regressed; a spurious `E-MC-ANY-001` with a clean parse
means `unsafe_caps` was dropped between `ExprKind.UnsafeBlock` and `HirBlock`.

## Compatibility and Limitations

Only the BLOCK form is carried on HIR. The declaration-level `@unsafe(...)`
annotation form still reaches the checker through `AnyEscapeProfile`.

## Scenarios

### unsafe(capabilities: [...]) block form

#### parses the block form into HirExprKind.UnsafeBlock carrying its capabilities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the block form into HirExprKind.UnsafeBlock carrying its capabilities
- lower the §8.1 primary-spelling fixture
- the statement IS an UnsafeBlock (pre-fix: plain expression statement)
   - Expected: caps.len() equals `1`
- and the body carries the parsed capability name
   - Expected: caps[0] equals `type_erasure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the block form into HirExprKind.UnsafeBlock carrying its capabilities")
step("lower the §8.1 primary-spelling fixture")
val caps = first_unsafe_caps(lower_fixture("block_form_type_erasure"))
step("the statement IS an UnsafeBlock (pre-fix: plain expression statement)")
expect(caps.len()).to_equal(1)
step("and the body carries the parsed capability name")
expect(caps[0]).to_equal("type_erasure")
```

</details>

#### treats Any inside a type_erasure block as granted without any profile grant

- treats Any inside a type_erasure block as granted without any profile grant
- check the fixture with an EMPTY grant list
- no origin report: the grant came from the HIR node
   - Expected: count_of(found, "E-MC-ANY-001/outside_unsafe") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats Any inside a type_erasure block as granted without any profile grant")
step("check the fixture with an EMPTY grant list")
val found = check_fixture("block_form_type_erasure")
step("no origin report: the grant came from the HIR node")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_equal(0)
```

</details>

#### still reports the origin when the block asks for raw_ptr only

- still reports the origin when the block asks for raw_ptr only
- check a block form granting raw_ptr but not type_erasure
- the Any inside is an E-MC-ANY-001 origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reports the origin when the block asks for raw_ptr only")
step("check a block form granting raw_ptr but not type_erasure")
val found = check_fixture("block_form_raw_ptr_only")
step("the Any inside is an E-MC-ANY-001 origin")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_be_greater_than(0)
```

</details>

#### reports an escape, not an origin, when the granted block returns its Any

- reports an escape, not an origin, when the granted block returns its Any
- check a type_erasure block that returns the erased value
   - Expected: count_of(found, "E-MC-ANY-001/outside_unsafe") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports an escape, not an origin, when the granted block returns its Any")
step("check a type_erasure block that returns the erased value")
val found = check_fixture("block_form_leak")
expect(count_of(found, "E-MC-ANY-002/escape_return")).to_be_greater_than(0)
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_equal(0)
```

</details>

#### does not grant erasure for an unknown capability name

- does not grant erasure for an unknown capability name
- check a block form whose capability is misspelled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not grant erasure for an unknown capability name")
step("check a block form whose capability is misspelled")
val found = check_fixture("block_form_unknown_cap")
expect(count_of(found, "E-MC-ANY-001/outside_unsafe")).to_be_greater_than(0)
```

</details>

#### keeps the bare `unsafe:` form as an UnsafeBlock with no capabilities

- keeps the bare `unsafe:` form as an UnsafeBlock with no capabilities
   - Expected: caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the bare `unsafe:` form as an UnsafeBlock with no capabilities")
val caps = first_unsafe_caps(lower_fixture("block_form_bare"))
expect(caps.len()).to_equal(0)
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


## Related Documentation

- **Research:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md §8.1`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MC-ANY-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d85ae78523e62e02e5961137a5ae88a486f27f064493c6b298e0df38dfcae2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d85ae78523e62e02e5961137a5ae88a486f27f064493c6b298e0df38dfcae2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d85ae78523e62e02e5961137a5ae88a486f27f064493c6b298e0df38dfcae2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the block form into HirExprKind.UnsafeBlock carrying its capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats Any inside a type_erasure block as granted without any profile grant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reports the origin when the block asks for raw_ptr only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
