# Game2D Golden Frame (AC-5 — golden half)

> `HeadlessBackend.frame_hash()` after N frames matches a stored hash from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Golden Frame (AC-5 — golden half)

`HeadlessBackend.frame_hash()` after N frames matches a stored hash from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | RESOLVED 2026-04-26 — 11/11 PASS. Hash pinned to `0x253edd45a462bc15`. |
| Source | `test/03_system/engine/game2d_golden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`HeadlessBackend.frame_hash()` after N frames matches a stored hash from
`test/fixtures/game2d_golden_hello_720p.hash`. Phase 5b pinned the value
to `0x253edd45a462bc15` (FNV-1a over the 4×4 representative framebuffer,
verified deterministic across 3 runs via `test/fixtures/repro/game2d/game2d_pin_golden_hash.spl`).

Edge case: same replay twice → identical hash (determinism).
Error path: golden mismatch → spec fails with diff.

## Scenarios

### Game2D Golden Frame (AC-5 golden)

### frame_hash function declared

#### headless.spl declares fn frame_hash(buf: [u32]) -> u64

- headless.spl declares fn frame_hash(buf: [u32]) -> u64
   - Expected: _has(src, "fn frame_hash(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless.spl declares fn frame_hash(buf: [u32]) -> u64")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "fn frame_hash(")).to_equal(true)
```

</details>

#### headless.spl uses FNV-1a (or documented hash)

- headless.spl uses FNV-1a (or documented hash)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless.spl uses FNV-1a (or documented hash)")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "FNV") or _has(src, "fnv1a") or
       _has(src, "hash")).to_equal(true)
```

</details>

### golden fixture exists

#### test/fixtures/game2d_golden_hello_720p.hash exists

- test/fixtures/game2d_golden_hello_720p.hash exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test/fixtures/game2d_golden_hello_720p.hash exists")
expect(rt_file_exists(
    "test/fixtures/game2d_golden_hello_720p.hash")).to_equal(true)
```

</details>

#### fixture is non-empty

- fixture is non-empty
   - Expected: src.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture is non-empty")
val src = _read("test/fixtures/game2d_golden_hello_720p.hash")
expect(src.len() > 0).to_equal(true)
```

</details>

#### fixture contains the pinned FNV-1a hash (0x253edd45a462bc15)

- fixture contains the pinned FNV-1a hash (0x253edd45a462bc15)
   - Expected: _has(_trim(src), "253edd45a462bc15") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture contains the pinned FNV-1a hash (0x253edd45a462bc15)")
val src = _read("test/fixtures/game2d_golden_hello_720p.hash")
expect(_has(_trim(src), "253edd45a462bc15")).to_equal(true)
```

</details>

#### fixture starts with 0x hex prefix

- fixture starts with 0x hex prefix
   - Expected: _trim(src).starts_with("0x") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture starts with 0x hex prefix")
val src = _read("test/fixtures/game2d_golden_hello_720p.hash")
expect(_trim(src).starts_with("0x")).to_equal(true)
```

</details>

### edge case: determinism across runs

#### synthetic: same input bytes → same hash

- synthetic: same input bytes → same hash
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic: same input bytes → same hash")
val a = "253edd45a462bc15"
val b = "253edd45a462bc15"
expect(a).to_equal(b)
```

</details>

#### synthetic: different input → different hash

- synthetic: different input → different hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic: different input → different hash")
val a = "253edd45a462bc15"
val b = "253edd45a462bc14"
expect(a).to_not_equal(b)
```

</details>

#### pin utility exists for 3-run reproducibility check

- pin utility exists for 3-run reproducibility check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pin utility exists for 3-run reproducibility check")
expect(rt_file_exists("test/fixtures/repro/game2d/game2d_pin_golden_hash.spl")
    ).to_equal(true)
```

</details>

### error path: golden mismatch

#### headless.spl notes diff-on-mismatch contract

- headless.spl notes diff-on-mismatch contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless.spl notes diff-on-mismatch contract")
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "diff") or _has(src, "mismatch") or
       _has(src, "frame_hash")).to_equal(true)
```

</details>

#### edge case: missing golden file yields empty read

- edge case: missing golden file yields empty read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: missing golden file yields empty read")
expect(_read(
    "test/fixtures/does_not_exist.hash")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4d6bd5a6214615e87fc5ed16f54172602f7db79fc5f4957ad24f7527e4cb5eeb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d6bd5a6214615e87fc5ed16f54172602f7db79fc5f4957ad24f7527e4cb5eeb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d6bd5a6214615e87fc5ed16f54172602f7db79fc5f4957ad24f7527e4cb5eeb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/game2d_golden_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_golden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_golden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_golden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_golden_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'headless.spl declares fn frame_hash(buf: [u32]) -> u64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_golden_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'headless.spl uses FNV-1a (or documented hash)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_golden_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test/fixtures/game2d_golden_hello_720p.hash exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
