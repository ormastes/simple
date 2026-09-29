# Runtime-Allocated Buffer Index Assignment Specification

> A buffer handed back by a runtime allocator (`rt_byte_array_new`,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime-Allocated Buffer Index Assignment Specification

A buffer handed back by a runtime allocator (`rt_byte_array_new`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A buffer handed back by a runtime allocator (`rt_byte_array_new`,
`rt_bytes_alloc`) is a packed byte array, not the generic array
representation. Until 2026-08-21 the interpreter's index-assignment path
recognised only the generic form, so `self.buf[i] = v` on such a buffer failed
with `invalid assignment: cannot index assign to field 'buf' of type array` —
a message that names the very type it refused. Every module that preallocates
a buffer and fills it slot-by-slot was pushed onto a dead path by that.

Regression cover for item 1 of
doc/08_tracking/bug/interpreter_raw_array_and_glob_import_gaps_2026-08-21.md.

## Scenarios

### runtime-allocated buffer index assignment

#### writes through a field holding a runtime-allocated buffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes through a field holding a runtime-allocated buffer
   - Expected: b.get(0) equals `7u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes through a field holding a runtime-allocated buffer")
val b = ByteBox.sized(4)
b.set(0, 7u8)
expect(b.get(0)).to_equal(7u8)
```

</details>

#### writes every slot of the buffer independently

- writes every slot of the buffer independently
   - Expected: b.get(0) equals `1u8`
   - Expected: b.get(1) equals `2u8`
   - Expected: b.get(2) equals `3u8`
   - Expected: b.get(3) equals `4u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes every slot of the buffer independently")
# The original defect made such a buffer effectively write-once, so
# filling it slot-by-slot -- the exact pattern the stdlib modules
# needed -- silently could not work.
val b = ByteBox.sized(4)
b.set(0, 1u8)
b.set(1, 2u8)
b.set(2, 3u8)
b.set(3, 4u8)
expect(b.get(0)).to_equal(1u8)
expect(b.get(1)).to_equal(2u8)
expect(b.get(2)).to_equal(3u8)
expect(b.get(3)).to_equal(4u8)
```

</details>

#### overwrites a slot that was already written

- overwrites a slot that was already written
   - Expected: b.get(0) equals `11u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("overwrites a slot that was already written")
val b = ByteBox.sized(2)
b.set(0, 9u8)
b.set(0, 11u8)
expect(b.get(0)).to_equal(11u8)
```

</details>

#### leaves the other slots untouched by a single write

- leaves the other slots untouched by a single write
   - Expected: b.get(0) equals `0u8`
   - Expected: b.get(1) equals `5u8`
   - Expected: b.get(2) equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves the other slots untouched by a single write")
val b = ByteBox.sized(3)
b.set(1, 5u8)
expect(b.get(0)).to_equal(0u8)
expect(b.get(1)).to_equal(5u8)
expect(b.get(2)).to_equal(0u8)
```

</details>

#### still supports index assignment into a Simple-built array

- still supports index assignment into a Simple-built array
   - Expected: xs[1] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still supports index assignment into a Simple-built array")
# The generic array path always worked; asserted so a fix for the
# packed representation cannot regress the one that was already right.
var xs: [i64] = [0, 0, 0]
xs[1] = 42
expect(xs[1]).to_equal(42)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `655439799c7ef7ff6702eb362a2aab726713962359c8328d27eff29fc3878b17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `655439799c7ef7ff6702eb362a2aab726713962359c8328d27eff29fc3878b17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `655439799c7ef7ff6702eb362a2aab726713962359c8328d27eff29fc3878b17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes through a field holding a runtime-allocated buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes every slot of the buffer independently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/runtime_buffer_index_assign_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overwrites a slot that was already written' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
