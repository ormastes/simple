# zero_forward_path_gate_spec

> Purpose: Prove that zero_forward_path gate — fail-closed contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# zero_forward_path_gate_spec

Purpose: Prove that zero_forward_path gate — fail-closed contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/zero_forward_path_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that zero_forward_path gate — fail-closed contract.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### zero_forward_path gate — fail-closed contract

#### BLOCKS an empty scan instead of reporting a vacuous pass

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- BLOCKS an empty scan instead of reporting a vacuous pass
- Verify: BLOCKS an empty scan instead of reporting a vacuous pass
   - Expected: v.scanned equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BLOCKS an empty scan instead of reporting a vacuous pass")
step("Verify: BLOCKS an empty scan instead of reporting a vacuous pass")
# @req: REQ-COMPILER-SEMANTICS-001
var none: [ZeroForwardEntry] = []
val v = check_all_zero_forward_paths(none)
assert_false(v.ok)
assert_true(v.blocked)
expect(v.scanned).to_equal(0)  # oracle: 0 — named expected value from the requirement
assert_true(v.reason.contains("scanned 0 entrypoints"))
```

</details>

#### BLOCKS a scan that examined entrypoints but found no @zero_forward_path claim

- BLOCKS a scan that examined entrypoints but found no @zero_forward_path claim
- Verify: BLOCKS a scan that examined entrypoints but found no @zero_forward_path claim
   - Expected: v.scanned equals `2`
   - Expected: v.gated equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BLOCKS a scan that examined entrypoints but found no @zero_forward_path claim")
step("Verify: BLOCKS a scan that examined entrypoints but found no @zero_forward_path claim")
val unclaimed = ZeroForwardEntry(
    entrypoint: "mod:hot", annotated: false,
    edges: [], temporary_allocations: 0, dynamic_dispatches: 0,
    batches: 1, unmeasured_axes: no_axes(), unmeasured_reason: "")
val v = check_all_zero_forward_paths([unclaimed, unclaimed])
assert_false(v.ok)
assert_true(v.blocked)
expect(v.scanned).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(v.gated).to_equal(0)  # oracle: 0 — named expected value from the requirement
assert_true(v.reason.contains("0 carry @zero_forward_path"))
```

</details>

#### PASSES only when a nonzero number of gated entrypoints are measured and clean

- PASSES only when a nonzero number of gated entrypoints are measured and clean
- Verify: PASSES only when a nonzero number of gated entrypoints are measured and clean
   - Expected: v.scanned equals `1`
   - Expected: v.gated equals `1`
   - Expected: v.violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PASSES only when a nonzero number of gated entrypoints are measured and clean")
step("Verify: PASSES only when a nonzero number of gated entrypoints are measured and clean")
val v = check_all_zero_forward_paths([clean_entry("mod:hot")])
assert_true(v.ok)
assert_false(v.blocked)
expect(v.scanned).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v.gated).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v.violations.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### zero_forward_path gate — unmeasured axes are BLOCKED, never zero

#### reports an unmeasured axis as ZFP_UNMEASURED with the producer's reason

- reports an unmeasured axis as ZFP_UNMEASURED with the producer's reason
- Verify: reports an unmeasured axis as ZFP_UNMEASURED with the producer's reason
   - Expected: vs.len() equals `1`
   - Expected: vs[0].kind equals `ZFP_UNMEASURED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports an unmeasured axis as ZFP_UNMEASURED with the producer's reason")
step("Verify: reports an unmeasured axis as ZFP_UNMEASURED with the producer's reason")
var e = clean_entry("mod:hot")
e.unmeasured_axes = [ZFP_AXIS_COPY_BYTES]
e.unmeasured_reason = "no post-collapse MIR"
val vs = check_zero_forward_entry(e)
expect(vs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(vs[0].kind).to_equal(ZFP_UNMEASURED)
assert_true(vs[0].detail.contains("no post-collapse MIR"))
val verdict = check_all_zero_forward_paths([e])
assert_false(verdict.ok)
assert_true(verdict.blocked)
```

</details>

#### rejects an unknown axis name so a typo cannot silently disable a check

- rejects an unknown axis name so a typo cannot silently disable a check
- Verify: rejects an unknown axis name so a typo cannot silently disable a check
   - Expected: vs[0].kind equals `ZFP_UNMEASURED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an unknown axis name so a typo cannot silently disable a check")
step("Verify: rejects an unknown axis name so a typo cannot silently disable a check")
var e = clean_entry("mod:hot")
e.unmeasured_axes = ["copybytes"]
assert_false(zfp_known_axis("copybytes"))
val vs = check_zero_forward_entry(e)
assert_true(vs.len() >= 1)
expect(vs[0].kind).to_equal(ZFP_UNMEASURED)
assert_true(vs[0].detail.contains("unknown axis name"))
```

</details>

#### treats a negative counter as a not-measured sentinel, not as zero

- treats a negative counter as a not-measured sentinel, not as zero
- Verify: treats a negative counter as a not-measured sentinel, not as zero
   - Expected: count_kind(e, ZFP_UNMEASURED) equals `1`
   - Expected: count_kind(e, ZFP_TEMPORARY_ALLOCATION) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a negative counter as a not-measured sentinel, not as zero")
step("Verify: treats a negative counter as a not-measured sentinel, not as zero")
var e = clean_entry("mod:hot")
e.temporary_allocations = 0 - 1
expect(count_kind(e, ZFP_UNMEASURED)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_kind(e, ZFP_TEMPORARY_ALLOCATION)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### treats a negative edge copy_bytes as a not-measured sentinel, not as zero

- treats a negative edge copy_bytes as a not-measured sentinel, not as zero
- Verify: treats a negative edge copy_bytes as a not-measured sentinel, not as zero
   - Expected: count_kind(e, ZFP_UNMEASURED) equals `1`
   - Expected: count_kind(e, ZFP_LAYER_VIEW_COPY) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a negative edge copy_bytes as a not-measured sentinel, not as zero")
step("Verify: treats a negative edge copy_bytes as a not-measured sentinel, not as zero")
var e = clean_entry("mod:hot")
e.edges = [ForwardEdge(from_symbol: "a", to_symbol: "b",
    physical: false, copy_bytes: 0 - 1)]
expect(count_kind(e, ZFP_UNMEASURED)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_kind(e, ZFP_LAYER_VIEW_COPY)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### BLOCKS the <=1/batch bound when batches is 0 (no divisor)

- BLOCKS the <=1/batch bound when batches is 0 (no divisor)
- Verify: BLOCKS the <=1/batch bound when batches is 0 (no divisor)
   - Expected: count_kind(e, ZFP_UNMEASURED) equals `1`
   - Expected: count_kind(e, ZFP_DYNAMIC_DISPATCH) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BLOCKS the <=1/batch bound when batches is 0 (no divisor)")
step("Verify: BLOCKS the <=1/batch bound when batches is 0 (no divisor)")
var e = clean_entry("mod:hot")
e.batches = 0
e.dynamic_dispatches = 3
expect(count_kind(e, ZFP_UNMEASURED)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_kind(e, ZFP_DYNAMIC_DISPATCH)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reports unmeasured counters as -1, never 0, in the §3 C5 report line

- reports unmeasured counters as -1, never 0, in the §3 C5 report line
- Verify: reports unmeasured counters as -1, never 0, in the §3 C5 report line
   - Expected: c.logical_forward_edges equals `1`
   - Expected: c.physical_forward_calls equals `0`
   - Expected: c.layer_view_copy_bytes equals `0 - 1`
   - Expected: c.temporary_allocations equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports unmeasured counters as -1, never 0, in the §3 C5 report line")
step("Verify: reports unmeasured counters as -1, never 0, in the §3 C5 report line")
var e = clean_entry("mod:hot")
e.unmeasured_axes = [ZFP_AXIS_COPY_BYTES, ZFP_AXIS_ALLOCATIONS]
val c = zero_forward_counters(e)
expect(c.logical_forward_edges).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(c.physical_forward_calls).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(c.layer_view_copy_bytes).to_equal(0 - 1)
expect(c.temporary_allocations).to_equal(0 - 1)
assert_true(format_zero_forward_counters(c).contains(
    "layer_view_copy_bytes=-1"))
```

</details>

### zero_forward_path gate — each axis bites

#### FAILS on a surviving physical forward call

- FAILS on a surviving physical forward call
- Verify: FAILS on a surviving physical forward call
   - Expected: zfp_physical_calls(e) equals `1`
   - Expected: count_kind(e, ZFP_PHYSICAL_FORWARD_CALL) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FAILS on a surviving physical forward call")
step("Verify: FAILS on a surviving physical forward call")
var e = clean_entry("mod:hot")
e.edges = [ForwardEdge(from_symbol: "WebPainter.submit",
    to_symbol: "GuiPainter.submit", physical: true, copy_bytes: 0)]
expect(zfp_physical_calls(e)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_kind(e, ZFP_PHYSICAL_FORWARD_CALL)).to_equal(1)  # oracle: 1 — named expected value from the requirement
val v = check_all_zero_forward_paths([e])
assert_false(v.ok)
assert_false(v.blocked)
assert_true(v.reason.contains("FAIL"))
```

</details>

#### FAILS on a nonzero layer-view copy

- FAILS on a nonzero layer-view copy
- Verify: FAILS on a nonzero layer-view copy
   - Expected: count_kind(e, ZFP_LAYER_VIEW_COPY) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FAILS on a nonzero layer-view copy")
step("Verify: FAILS on a nonzero layer-view copy")
var e = clean_entry("mod:hot")
e.edges = [ForwardEdge(from_symbol: "GuiBounds", to_symbol: "DeviceRect",
    physical: false, copy_bytes: 16)]
expect(count_kind(e, ZFP_LAYER_VIEW_COPY)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### FAILS on a temporary allocation

- FAILS on a temporary allocation
- Verify: FAILS on a temporary allocation
   - Expected: count_kind(e, ZFP_TEMPORARY_ALLOCATION) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FAILS on a temporary allocation")
step("Verify: FAILS on a temporary allocation")
var e = clean_entry("mod:hot")
e.temporary_allocations = 1
expect(count_kind(e, ZFP_TEMPORARY_ALLOCATION)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### FAILS when dynamic dispatches exceed 1 per batch

- FAILS when dynamic dispatches exceed 1 per batch
- Verify: FAILS when dynamic dispatches exceed 1 per batch
   - Expected: count_kind(e, ZFP_DYNAMIC_DISPATCH) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FAILS when dynamic dispatches exceed 1 per batch")
step("Verify: FAILS when dynamic dispatches exceed 1 per batch")
var e = clean_entry("mod:hot")
e.dynamic_dispatches = 5
e.batches = 4
expect(count_kind(e, ZFP_DYNAMIC_DISPATCH)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### allows exactly 1 dispatch per batch (the bound is <=, not <)

- allows exactly 1 dispatch per batch (the bound is <=, not <)
- Verify: allows exactly 1 dispatch per batch (the bound is <=, not <)
   - Expected: count_kind(e, ZFP_DYNAMIC_DISPATCH) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows exactly 1 dispatch per batch (the bound is <=, not <)")
step("Verify: allows exactly 1 dispatch per batch (the bound is <=, not <)")
var e = clean_entry("mod:hot")
e.dynamic_dispatches = 4
e.batches = 4
expect(count_kind(e, ZFP_DYNAMIC_DISPATCH)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### formats a violation with the error[zero_forward_path] prefix

- formats a violation with the error[zero_forward_path] prefix
- Verify: formats a violation with the error[zero_forward_path] prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats a violation with the error[zero_forward_path] prefix")
step("Verify: formats a violation with the error[zero_forward_path] prefix")
var e = clean_entry("mod:hot")
e.temporary_allocations = 2
val vs = check_zero_forward_entry(e)
assert_true(format_zfp_violation(vs[0]).starts_with(
    "error[zero_forward_path]: mod:hot: temporary_allocation"))
```

</details>

### zero_forward_path gate — hop axis is independently gatable today

#### PASSES the hop axis when every hop collapsed, even with MIR axes unmeasured

- PASSES the hop axis when every hop collapsed, even with MIR axes unmeasured
- Verify: PASSES the hop axis when every hop collapsed, even with MIR axes unmeasured
   - Expected: h.gated equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PASSES the hop axis when every hop collapsed, even with MIR axes unmeasured")
step("Verify: PASSES the hop axis when every hop collapsed, even with MIR axes unmeasured")
var e = clean_entry("mod:hot")
e.unmeasured_axes = [ZFP_AXIS_COPY_BYTES, ZFP_AXIS_ALLOCATIONS,
    ZFP_AXIS_DISPATCH]
e.unmeasured_reason = "no post-collapse MIR"
# Full gate: BLOCKED. Hop axis alone: PASS.
assert_true(check_all_zero_forward_paths([e]).blocked)
val h = hop_axis_verdict([e])
assert_true(h.ok)
expect(h.gated).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### FAILS the hop axis on a surviving physical hop

- FAILS the hop axis on a surviving physical hop
- Verify: FAILS the hop axis on a surviving physical hop


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FAILS the hop axis on a surviving physical hop")
step("Verify: FAILS the hop axis on a surviving physical hop")
var e = clean_entry("mod:hot")
e.unmeasured_axes = [ZFP_AXIS_COPY_BYTES, ZFP_AXIS_ALLOCATIONS,
    ZFP_AXIS_DISPATCH]
e.edges = [ForwardEdge(from_symbol: "a", to_symbol: "b",
    physical: true, copy_bytes: 0 - 1)]
val h = hop_axis_verdict([e])
assert_false(h.ok)
assert_false(h.blocked)
```

</details>

#### BLOCKS the hop axis when the producer could not enumerate hops

- BLOCKS the hop axis when the producer could not enumerate hops
- Verify: BLOCKS the hop axis when the producer could not enumerate hops


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BLOCKS the hop axis when the producer could not enumerate hops")
step("Verify: BLOCKS the hop axis when the producer could not enumerate hops")
var e = clean_entry("mod:hot")
e.unmeasured_axes = [ZFP_AXIS_HOPS]
e.unmeasured_reason = "blanket alias not enumerable from text"
val h = hop_axis_verdict([e])
assert_false(h.ok)
assert_true(h.blocked)
```

</details>

#### BLOCKS the hop axis on an empty scan

- BLOCKS the hop axis on an empty scan
- Verify: BLOCKS the hop axis on an empty scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BLOCKS the hop axis on an empty scan")
step("Verify: BLOCKS the hop axis on an empty scan")
var none: [ZeroForwardEntry] = []
assert_true(hop_axis_verdict(none).blocked)
```

</details>

### forward_hop_scan — declaration parsing

#### parses `alias fn NAME = FIELD.METHOD`

- parses `alias fn NAME = FIELD.METHOD`
- Verify: parses `alias fn NAME = FIELD.METHOD`
   - Expected: ds.len() equals `1`
   - Expected: ds[0].logical_name equals `len`
   - Expected: ds[0].receiver_field equals `inner`
   - Expected: ds[0].target_method equals `len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses `alias fn NAME = FIELD.METHOD`")
step("Verify: parses `alias fn NAME = FIELD.METHOD`")
val ds = parse_forward_decl("    alias fn len = inner.len")
expect(ds.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(ds[0].logical_name).to_equal("len")
expect(ds[0].receiver_field).to_equal("inner")
expect(ds[0].target_method).to_equal("len")
```

</details>

#### parses `alias me NAME(args) = FIELD.METHOD`

- parses `alias me NAME(args) = FIELD.METHOD`
- Verify: parses `alias me NAME(args) = FIELD.METHOD`
   - Expected: ds.len() equals `1`
   - Expected: ds[0].logical_name equals `set`
   - Expected: ds[0].receiver_field equals `inner`
   - Expected: ds[0].target_method equals `store`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses `alias me NAME(args) = FIELD.METHOD`")
step("Verify: parses `alias me NAME(args) = FIELD.METHOD`")
val ds = parse_forward_decl("    alias me set(key, v) = inner.store")
expect(ds.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(ds[0].logical_name).to_equal("set")
expect(ds[0].receiver_field).to_equal("inner")
expect(ds[0].target_method).to_equal("store")
```

</details>

#### does not fabricate a declaration from a non-alias line

- does not fabricate a declaration from a non-alias line
- Verify: does not fabricate a declaration from a non-alias line
   - Expected: parse_forward_decl("fn len(): 0").len() equals `0`
   - Expected: parse_forward_decl("# alias fn len = inner.len").len() equals `0`
   - Expected: parse_forward_decl("alias fn len = inner").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fabricate a declaration from a non-alias line")
step("Verify: does not fabricate a declaration from a non-alias line")
expect(parse_forward_decl("fn len(): 0").len()).to_equal(0)
expect(parse_forward_decl("# alias fn len = inner.len").len()).to_equal(0)
expect(parse_forward_decl("alias fn len = inner").len()).to_equal(0)
```

</details>

### forward_hop_scan — real source text, nonzero scanned count

#### extracts a two-hop chain and gates it RED on the hop axis

- extracts a two-hop chain and gates it RED on the hop axis
- Verify: extracts a two-hop chain and gates it RED on the hop axis
   - Expected: entries.len() equals `1`
   - Expected: entries[0].entrypoint equals `probe.spl:submit`
   - Expected: entries[0].edges.len() equals `2`
   - Expected: zfp_physical_calls(entries[0]) equals `2`
   - Expected: h.scanned equals `1`
   - Expected: h.gated equals `1`
   - Expected: h.violations.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts a two-hop chain and gates it RED on the hop axis")
step("Verify: extracts a two-hop chain and gates it RED on the hop axis")
val src = "class WebPainter:\n"
    + "    inner: GuiPainter\n"
    + "    @zero_forward_path\n"
    + "    alias fn submit = inner.forward_submit\n"
    + "    alias fn forward_submit = backend.execute\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(entries[0].entrypoint).to_equal("probe.spl:submit")
# Two physical hops survive: submit -> inner.forward_submit ->
# backend.execute. Neither is collapsed (no collapse pass exists).
expect(entries[0].edges.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(zfp_physical_calls(entries[0])).to_equal(2)  # oracle: 2 — named expected value from the requirement
val h = hop_axis_verdict(entries)
assert_true(h.scanned > 0)
expect(h.scanned).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(h.gated).to_equal(1)  # oracle: 1 — named expected value from the requirement
assert_false(h.ok)
expect(h.violations.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### declares the three MIR-only axes unmeasured, so the FULL gate BLOCKS

- declares the three MIR-only axes unmeasured, so the FULL gate BLOCKS
- Verify: declares the three MIR-only axes unmeasured, so the FULL gate BLOCKS
   - Expected: entries.len() equals `1`
   - Expected: entries[0].temporary_allocations equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares the three MIR-only axes unmeasured, so the FULL gate BLOCKS")
step("Verify: declares the three MIR-only axes unmeasured, so the FULL gate BLOCKS")
val src = "class P:\n"
    + "    @zero_forward_path\n"
    + "    alias fn submit = inner.execute\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(entries[0].temporary_allocations).to_equal(0 - 1)
val v = check_all_zero_forward_paths(entries)
assert_true(v.scanned > 0)
assert_false(v.ok)
assert_true(v.blocked)
```

</details>

#### declares the HOP axis unmeasured when a blanket alias hides the method set

- declares the HOP axis unmeasured when a blanket alias hides the method set
- Verify: declares the HOP axis unmeasured when a blanket alias hides the method set
   - Expected: entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares the HOP axis unmeasured when a blanket alias hides the method set")
step("Verify: declares the HOP axis unmeasured when a blanket alias hides the method set")
val src = "class P:\n"
    + "    alias inner\n"
    + "    @zero_forward_path\n"
    + "    alias fn submit = inner.execute\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val h = hop_axis_verdict(entries)
assert_true(h.scanned > 0)
assert_false(h.ok)
assert_true(h.blocked)
```

</details>

#### reports a collapsed-looking entrypoint with ZERO hops as hop-axis GREEN

- reports a collapsed-looking entrypoint with ZERO hops as hop-axis GREEN
- Verify: reports a collapsed-looking entrypoint with ZERO hops as hop-axis GREEN
   - Expected: entries.len() equals `1`
   - Expected: entries[0].edges.len() equals `0`
   - Expected: h.gated equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a collapsed-looking entrypoint with ZERO hops as hop-axis GREEN")
step("Verify: reports a collapsed-looking entrypoint with ZERO hops as hop-axis GREEN")
# An annotated entrypoint with no alias forwarding at all has zero
# logical edges, hence zero physical hops. This is the ONLY shape that
# is currently hop-axis green, and it is green for a real reason.
val src = "class P:\n"
    + "    @zero_forward_path\n"
    + "    fn submit(): backend_execute()\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(entries[0].edges.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
val h = hop_axis_verdict(entries)
assert_true(h.scanned > 0)
assert_true(h.ok)
expect(h.gated).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### finds NO entrypoint in source with no @zero_forward_path, and BLOCKS

- finds NO entrypoint in source with no @zero_forward_path, and BLOCKS
- Verify: finds NO entrypoint in source with no @zero_forward_path, and BLOCKS
   - Expected: entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds NO entrypoint in source with no @zero_forward_path, and BLOCKS")
step("Verify: finds NO entrypoint in source with no @zero_forward_path, and BLOCKS")
val src = "class P:\n    alias fn submit = inner.execute\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
assert_true(check_all_zero_forward_paths(entries).blocked)
```

</details>

#### does not attribute a decorator to a following non-callable declaration

- does not attribute a decorator to a following non-callable declaration
- Verify: does not attribute a decorator to a following non-callable declaration
   - Expected: scan_source_forward_hops("probe.spl", src).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not attribute a decorator to a following non-callable declaration")
step("Verify: does not attribute a decorator to a following non-callable declaration")
val src = "@zero_forward_path\nstruct NotAFn:\n    x: i32\n"
    + "fn unrelated(): 0\n"
expect(scan_source_forward_hops("probe.spl", src).len()).to_equal(0)
```

</details>

#### terminates on a cyclic alias chain instead of hanging

- terminates on a cyclic alias chain instead of hanging
- Verify: terminates on a cyclic alias chain instead of hanging
   - Expected: entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("terminates on a cyclic alias chain instead of hanging")
step("Verify: terminates on a cyclic alias chain instead of hanging")
val src = "class P:\n"
    + "    @zero_forward_path\n"
    + "    alias fn a = inner.b\n"
    + "    alias fn b = inner.a\n"
val entries = scan_source_forward_hops("probe.spl", src)
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
assert_true(entries[0].edges.len() >= 1)
assert_true(entries[0].edges.len() <= 3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-SEMANTICS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `977557d81c45e5cb3e6af73eef9febf7291ba57a9b710d3b45c1b364d7b186c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `977557d81c45e5cb3e6af73eef9febf7291ba57a9b710d3b45c1b364d7b186c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `977557d81c45e5cb3e6af73eef9febf7291ba57a9b710d3b45c1b364d7b186c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/zero_forward_path_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/zero_forward_path_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/zero_forward_path_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/zero_forward_path_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/zero_forward_path_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/zero_forward_path_gate_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BLOCKS an empty scan instead of reporting a vacuous pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/zero_forward_path_gate_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BLOCKS a scan that examined entrypoints but found no @zero_forward_path claim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/zero_forward_path_gate_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PASSES only when a nonzero number of gated entrypoints are measured and clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
