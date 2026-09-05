# Wine Simpleos Window Bridge Specification

> Tests covering Wine SimpleOS window bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Simpleos Window Bridge Specification

## Scenarios

### Wine SimpleOS window bridge

#### starts with only SimpleOS winfs evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with only SimpleOS winfs evidence
   - Expected: wine_simpleos_window_bridge_gate(bridge) equals `missing-simpleos-window-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts with only SimpleOS winfs evidence")
val bridge = wine_simpleos_window_bridge_new()
expect(wine_simpleos_window_bridge_gate(bridge)).to_equal("missing-simpleos-window-record")
```

</details>

#### creates WindowRecord framebuffer metadata

- creates WindowRecord framebuffer metadata
   - Expected: created.ok is true
   - Expected: created.record.buffer_ref.kind equals `simpleos-framebuffer`
   - Expected: created.record.buffer_ref.bytes equals `256000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates WindowRecord framebuffer metadata")
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 42, "wine", "hello", 320, 200)
expect(created.ok).to_equal(true)
expect(created.record.buffer_ref.kind).to_equal("simpleos-framebuffer")
expect(created.record.buffer_ref.bytes).to_equal(256000)
```

</details>

#### rejects invalid and missing window operations with structured states

- rejects invalid and missing window operations with structured states
   - Expected: invalid.state equals `invalid-window`
   - Expected: missing.state equals `missing-window`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid and missing window operations with structured states")
val invalid = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 0, "wine", "bad", 320, 200)
expect(invalid.state).to_equal("invalid-window")
val missing = wine_simpleos_map_window(wine_simpleos_window_bridge_new(), 99)
expect(missing.state).to_equal("missing-window")
```

</details>

#### records deterministic present checksum evidence

- records deterministic present checksum evidence
   - Expected: presented.bridge.checksum equals `406`
   - Expected: wine_simpleos_window_bridge_gate(presented.bridge) equals `missing-unmap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records deterministic present checksum evidence")
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 10, 10)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val presented = wine_simpleos_present_window(mapped.bridge, 1, 5)
expect(presented.bridge.checksum).to_equal(406)
expect(wine_simpleos_window_evidence(presented.bridge)).to_contain("framebuffer-checksum")
expect(wine_simpleos_window_bridge_gate(presented.bridge)).to_equal("missing-unmap")
```

</details>

#### requires SimpleOS cursor and clipboard evidence before X11 bridge readiness

- requires SimpleOS cursor and clipboard evidence before X11 bridge readiness
   - Expected: wine_simpleos_window_bridge_gate(destroyed.bridge) equals `missing-cursor`
   - Expected: wine_simpleos_window_bridge_gate(cursor.bridge) equals `missing-clipboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires SimpleOS cursor and clipboard evidence before X11 bridge readiness")
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 320, 200)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val configured = wine_simpleos_configure_window(mapped.bridge, 1, 10, 20, 640, 480)
val focused = wine_simpleos_focus_window(configured.bridge, 1)
val presented = wine_simpleos_present_window(focused.bridge, 1, 7)
val unmapped = wine_simpleos_unmap_window(presented.bridge, 1)
val destroyed = wine_simpleos_destroy_window(unmapped.bridge, 1)
expect(wine_simpleos_window_bridge_gate(destroyed.bridge)).to_equal("missing-cursor")
val cursor = wine_simpleos_set_cursor(destroyed.bridge, "arrow")
expect(wine_simpleos_window_bridge_gate(cursor.bridge)).to_equal("missing-clipboard")
```

</details>

#### unmaps WindowRecord state without destroying the record

- unmaps WindowRecord state without destroying the record
   - Expected: unmapped.ok is true
   - Expected: unmapped.state equals `unmapped`
   - Expected: unmapped.record.state equals `WindowState.Hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unmaps WindowRecord state without destroying the record")
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 10, 10)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val unmapped = wine_simpleos_unmap_window(mapped.bridge, 1)
expect(unmapped.ok).to_equal(true)
expect(unmapped.state).to_equal("unmapped")
expect(unmapped.record.state).to_equal(WindowState.Hidden)
expect(wine_simpleos_window_evidence(unmapped.bridge)).to_contain("unmap")
```

</details>

#### reaches the production bridge gate after lifecycle operations

- reaches the production bridge gate after lifecycle operations
   - Expected: destroyed.record.state equals `WindowState.Destroyed`
   - Expected: wine_simpleos_window_bridge_gate(destroyed.bridge) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reaches the production bridge gate after lifecycle operations")
val destroyed = _ready_bridge()
expect(destroyed.record.state).to_equal(WindowState.Destroyed)
expect(wine_simpleos_window_bridge_gate(destroyed.bridge)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine SimpleOS window bridge.
- Wine SimpleOS window bridge

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ade4277d8c6e16a8f18d254c78a2858e4b0e24f8624e96777b3969323f568e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ade4277d8c6e16a8f18d254c78a2858e4b0e24f8624e96777b3969323f568e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ade4277d8c6e16a8f18d254c78a2858e4b0e24f8624e96777b3969323f568e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with only SimpleOS winfs evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates WindowRecord framebuffer metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid and missing window operations with structured states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
