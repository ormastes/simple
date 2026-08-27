# Claude Full CircularBuffer

> Mirrors `tmp/claude/claude-code-main/src/utils/CircularBuffer.ts` for fixed-size

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CircularBuffer

Mirrors `tmp/claude/claude-code-main/src/utils/CircularBuffer.ts` for fixed-size

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/utils/CircularBuffer.ts` for fixed-size
rolling-window behavior: append, append many, overflow eviction, recent reads,
array conversion, length, and clear.

## Scenarios

### Claude full utils CircularBuffer

#### stores items in insertion order until capacity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores items in insertion order until capacity
- Add fewer items than capacity and read them back oldest to newest
   - Expected: buffer.length() equals `2`
   - Expected: buffer.toArray() equals `["a", "b"]`
   - Expected: buffer.getRecent(5) equals `["a", "b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores items in insertion order until capacity")
step("Add fewer items than capacity and read them back oldest to newest")
val buffer = circularBufferNew(3)
buffer.add("a")
buffer.add("b")

expect(buffer.length()).to_equal(2)
expect(buffer.toArray()).to_equal(["a", "b"])
expect(buffer.getRecent(5)).to_equal(["a", "b"])
```

</details>

#### evicts the oldest items when full

- evicts the oldest items when full
- Fill the buffer, overflow it, and preserve newest capacity items
   - Expected: buffer.length() equals `3`
   - Expected: buffer.toArray() equals `["c", "d", "e"]`
   - Expected: buffer.getRecent(2) equals `["d", "e"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evicts the oldest items when full")
step("Fill the buffer, overflow it, and preserve newest capacity items")
val buffer = CircularBuffer.new(3)
buffer.addAll(["a", "b", "c", "d", "e"])

expect(buffer.length()).to_equal(3)
expect(buffer.toArray()).to_equal(["c", "d", "e"])
expect(buffer.getRecent(2)).to_equal(["d", "e"])
```

</details>

#### returns empty arrays for empty, zero recent count, and clear

- returns empty arrays for empty, zero recent count, and clear
- Exercise the empty and cleared states
   - Expected: buffer.toArray() equals `[]`
   - Expected: buffer.getRecent(1) equals `[]`
   - Expected: buffer.getRecent(0) equals `[]`
   - Expected: buffer.length() equals `0`
   - Expected: buffer.toArray() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty arrays for empty, zero recent count, and clear")
step("Exercise the empty and cleared states")
val buffer = CircularBuffer.new(2)
expect(buffer.toArray()).to_equal([])
expect(buffer.getRecent(1)).to_equal([])

buffer.addAll(["x", "y"])
expect(buffer.getRecent(0)).to_equal([])
buffer.clear()

expect(buffer.length()).to_equal(0)
expect(buffer.toArray()).to_equal([])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `5d5fc226a22334c4bf3146be31b05f538341e31abc738c31f44c5482814773e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d5fc226a22334c4bf3146be31b05f538341e31abc738c31f44c5482814773e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d5fc226a22334c4bf3146be31b05f538341e31abc738c31f44c5482814773e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores items in insertion order until capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evicts the oldest items when full' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty arrays for empty, zero recent count, and clear' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
