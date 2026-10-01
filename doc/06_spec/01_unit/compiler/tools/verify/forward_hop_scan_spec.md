# Forward Hop Scan Specification

> Tests covering forward_hop_scan splits a forwarding target on the last dot, forward_hop_scan hop count follows the real target method.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Forward Hop Scan Specification

## Scenarios

### forward_hop_scan splits a forwarding target on the last dot

#### keeps a single-segment target intact (control: both parsers agree)
#### reads a two-segment target as projection inner.items and method push

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First-dot split reports field=inner, method=items — an
# intermediate field mistaken for the method, real target dropped.
val d = parse_forward_decl("    alias fn push = inner.items.push")
expect(d.len()).to_equal(1)
expect(d[0].logical_name).to_equal("push")
expect(d[0].receiver_field).to_equal("inner.items")
expect(d[0].target_method).to_equal("push")
```

</details>

#### reads a three-segment target as projection a.b.c and method d

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First-dot split reports field=a, method=b. A last-dot split that
# still runs a single-identifier prefix over the receiver half
# reports field=a, method=d — also red here.
val d = parse_forward_decl("    alias me deep = a.b.c.d")
expect(d.len()).to_equal(1)
expect(d[0].logical_name).to_equal("deep")
expect(d[0].receiver_field).to_equal("a.b.c")
expect(d[0].target_method).to_equal("d")
```

</details>

#### reports no declaration for a dotless target, matching the generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# forwarding.spl returns empty_result when find_last_char finds no
# dot; a scan that fabricated field/method here would invent a hop.
val d = parse_forward_decl("    alias fn bare = push")
expect(d.len()).to_equal(0)
```

</details>

### forward_hop_scan hop count follows the real target method

#### walks a two-hop chain whose first link has a multi-segment target

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `draw` forwards through inner.gfx to `render`, and `render`
# forwards again to backend.flush — two physical hops.
# Under the first-dot split the walk continues from `gfx` (an
# intermediate field), finds no declaration by that name, and stops
# after ONE edge: hops = 1 instead of 2, and the first edge reads
# `draw -> inner.gfx` instead of `draw -> inner.gfx.render`.
val src = "class C:\n"
    + "    @zero_forward_path\n"
    + "    alias fn draw = inner.gfx.render\n"
    + "    alias fn render = backend.flush\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)
expect(entries[0].entrypoint).to_equal("probe.spl:draw")
expect(entries[0].edges.len()).to_equal(2)
expect(entries[0].edges[0].from_symbol).to_equal("draw")
expect(entries[0].edges[0].to_symbol).to_equal("inner.gfx.render")
expect(entries[0].edges[1].from_symbol).to_equal("render")
expect(entries[0].edges[1].to_symbol).to_equal("backend.flush")
```

</details>

#### does not follow a declaration named after an intermediate field

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `items` here is a sibling forwarder, NOT the target of `push`.
# The first-dot split reports push's method as `items` and so walks
# into it, inventing a second hop that the generated code does not
# contain: hops = 2 instead of the correct 1.
val src = "class C:\n"
    + "    @zero_forward_path\n"
    + "    alias fn push = inner.items.push\n"
    + "    alias fn items = store.items\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)
expect(entries[0].edges.len()).to_equal(1)
expect(entries[0].edges[0].to_symbol).to_equal("inner.items.push")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering forward_hop_scan splits a forwarding target on the last dot, forward_hop_scan hop count follows the real target method.
- forward_hop_scan splits a forwarding target on the last dot
- forward_hop_scan hop count follows the real target method

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ccca4ab40caed703b6ab95b074d80ab1e04d75f697668227a5a1672dbb9bfc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ccca4ab40caed703b6ab95b074d80ab1e04d75f697668227a5a1672dbb9bfc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ccca4ab40caed703b6ab95b074d80ab1e04d75f697668227a5a1672dbb9bfc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl
mirror: doc/06_spec/01_unit/compiler/tools/verify/forward_hop_scan_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/tools/verify/forward_hop_scan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tools/verify/forward_hop_scan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps a single-segment target intact (control: both parsers agree)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:79:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads a two-segment target as projection inner.items and method push' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:89:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads a three-segment target as projection a.b.c and method d' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl:100:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports no declaration for a dotless target, matching the generator' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
