# Unsafe capability vocabulary

> `src/compiler/00.common/assurance/unsafe_capabilities.spl` is the single typed

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsafe capability vocabulary

`src/compiler/00.common/assurance/unsafe_capabilities.spl` is the single typed

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | In Progress |
| Research | doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md |
| Source | `test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`src/compiler/00.common/assurance/unsafe_capabilities.spl` is the single typed
table of capabilities an `unsafe` region may carry. Plan §8.1 adds
`type_erasure` to it; §20.3 row A5 sets the exit gate as a parser/model
roundtrip.

## Scope and Preconditions

Pure table: zero imports, zero module state. Nothing here parses source.

## Primary Workflow

Every variant renders to a canonical snake_case spelling and parses back to the
same variant. Unknown names are rejected, never mapped to a fallback.

## Key Concepts

| Concept | Description |
|---------|-------------|
| capability | A permission that widens what an `unsafe` region may do |
| `type_erasure` | The capability that licenses `Any` (§8.1) |

## Related Specifications

- doc/08_tracking/bug/unsafe_capabilities_not_carried_into_hir_2026-08-21.md

## Evidence and Provenance

The three pre-existing spellings (`raw_ptr`, `ffi`, `mmio`) are the ones already
written in `10.frontend/core/_ParserDecls/enum_module_body.spl:941`; they are
preserved verbatim so existing `@unsafe(capabilities: [...])` text round-trips.

## Recovery and Troubleshooting

An unknown capability name yields `nil` from `parse_unsafe_capability` and is
listed by `unknown_unsafe_capability_names`, so a typo is reportable rather than
silently denied.

## Compatibility and Limitations

Nothing validates capability names at parse time yet — see the bug record above.

## Scenarios

### Unsafe capability vocabulary

#### carries type_erasure as a real member of the table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries type_erasure as a real member of the table
- look type_erasure up by its canonical spelling
- it renders back to the same spelling
   - Expected: unsafe_capability_name(UnsafeCapability.TypeErasure) equals `type_erasure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries type_erasure as a real member of the table")
step("look type_erasure up by its canonical spelling")
expect(is_known_unsafe_capability("type_erasure")).to_be_true()
step("it renders back to the same spelling")
expect(unsafe_capability_name(UnsafeCapability.TypeErasure)).to_equal("type_erasure")
```

</details>

#### round-trips every capability through its canonical spelling

- round-trips every capability through its canonical spelling
- render then parse each variant in the table
   - Expected: unsafe_capability_name(parsed!) equals `unsafe_capability_name(cap)`
- the walk was not vacuous
   - Expected: round_tripped equals `all_unsafe_capabilities().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every capability through its canonical spelling")
step("render then parse each variant in the table")
var round_tripped = 0
for cap in all_unsafe_capabilities():
    val parsed = parse_unsafe_capability(unsafe_capability_name(cap))
    expect(parsed != nil).to_be_true()
    expect(unsafe_capability_name(parsed!)).to_equal(unsafe_capability_name(cap))
    round_tripped = round_tripped + 1
step("the walk was not vacuous")
expect(round_tripped).to_equal(all_unsafe_capabilities().len())
```

</details>

#### keeps the three spellings the parser already documents

- keeps the three spellings the parser already documents
- raw_ptr, ffi and mmio remain known


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the three spellings the parser already documents")
step("raw_ptr, ffi and mmio remain known")
expect(is_known_unsafe_capability("raw_ptr")).to_be_true()
expect(is_known_unsafe_capability("ffi")).to_be_true()
expect(is_known_unsafe_capability("mmio")).to_be_true()
```

</details>

#### rejects an unknown capability instead of falling back

- rejects an unknown capability instead of falling back
- parse a name that is in no table
- and it is reported rather than dropped
   - Expected: unknown_unsafe_capability_names(["ffi", "teleportation"]).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown capability instead of falling back")
step("parse a name that is in no table")
expect(parse_unsafe_capability("teleportation") == nil).to_be_true()
step("and it is reported rather than dropped")
expect(unknown_unsafe_capability_names(["ffi", "teleportation"]).len()).to_equal(1)
```

</details>

#### answers grant questions over the parser's raw text list

- answers grant questions over the parser's raw text list
- a list naming type_erasure grants it
- a list without it does not
- an unknown name grants nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers grant questions over the parser's raw text list")
step("a list naming type_erasure grants it")
expect(unsafe_capability_set_contains(["raw_ptr", "type_erasure"], UnsafeCapability.TypeErasure)).to_be_true()
step("a list without it does not")
expect(unsafe_capability_set_contains(["raw_ptr", "ffi"], UnsafeCapability.TypeErasure)).to_be_false()
step("an unknown name grants nothing")
expect(unsafe_capability_set_contains(["type_erasure_x"], UnsafeCapability.TypeErasure)).to_be_false()
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

- **Research:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MC-ANY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5262618aa61d8652d6402e329c89e08af79e6210cfde7db714175bd610318860`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5262618aa61d8652d6402e329c89e08af79e6210cfde7db714175bd610318860`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5262618aa61d8652d6402e329c89e08af79e6210cfde7db714175bd610318860`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl
mirror: doc/06_spec/unit/compiler/common/assurance/unsafe_capabilities_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/unit/compiler/common/assurance/unsafe_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries type_erasure as a real member of the table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every capability through its canonical spelling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the three spellings the parser already documents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
