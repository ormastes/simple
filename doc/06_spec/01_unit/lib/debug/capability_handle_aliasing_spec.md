# Capability-handle aliasing survives every acquisition shape

> A capability handle (`ref_debug_profiler(session)` and friends) is a HANDLE, not

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability-handle aliasing survives every acquisition shape

A capability handle (`ref_debug_profiler(session)` and friends) is a HANDLE, not

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/capability_handle_aliasing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A capability handle (`ref_debug_profiler(session)` and friends) is a HANDLE, not
a snapshot. Mutating it must be visible through the session that owns the
target, no matter where the acquiring call sits syntactically.

## Scope and Preconditions

Interpreter engine — this is where the defect lived. The reported rule was that
the acquisition's *syntactic position relative to the frame holding the session*
decided whether mutations survived: a free function's TAIL expression aliased,
while an acquisition bound to a local in the session's own frame, inlined into a
constructor there, or returned inside a struct, silently did not.

The partial survival is what made it dangerous. Mutations to a class-typed
SUB-OBJECT survived, so stepping looked correct, while the target's own array
field (`breaks`) and own bool field (`armed`) were silently discarded.

Root cause was in the interpreter's by-value receiver write-back, fixed by
`merge_shared_collection_fields`
(`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:975`),
which propagates Array/Dict/ByteArray fields from callee back to caller while
deliberately keeping scalars and nested structs value-typed.

## Primary Workflow

Build a session owning a target, acquire a handle in each of the four shapes,
mutate all three field KINDS through the handle, then read back through the
ORIGINAL session. Every shape must show every mutation.

## Key Concepts

| Concept | Description |
|---------|-------------|
| acquisition shape | where the acquiring call sits relative to the session's frame |
| field kind | scalar / array / bool — each had a different survival rule |
| read-back oracle | always through the original session, never the handle |

## Evidence and Provenance

Shapes and field kinds are taken verbatim from the bug doc's own two matrices.

## Scenarios

### capability handle aliasing

### the control shape the bug report found WORKING

#### propagates every field kind when acquired as a free fn tail expression

- propagates every field kind when acquired as a free fn tail expression
   - Expected: mutate(h: acquire(s: s)) is true
   - Expected: steps_of(s: s) equals `1`
   - Expected: breaks_of(s: s) equals `1`
   - Expected: armed_of(s: s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates every field kind when acquired as a free fn tail expression")
val s = DbgSession.new()
expect(mutate(h: acquire(s: s))).to_equal(true)
expect(steps_of(s: s)).to_equal(1)
expect(breaks_of(s: s)).to_equal(1)
expect(armed_of(s: s)).to_equal(true)
```

</details>

### the three shapes the bug report found BROKEN

#### propagates when the handle is bound to a local in the session's own frame

- propagates when the handle is bound to a local in the session's own frame
   - Expected: mutate(h: acquired) is true
   - Expected: steps_of(s: s) equals `1`
   - Expected: breaks_of(s: s) equals `1`
   - Expected: armed_of(s: s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates when the handle is bound to a local in the session's own frame")
val s = DbgSession.new()
val acquired = acquire(s: s)
expect(mutate(h: acquired)).to_equal(true)
expect(steps_of(s: s)).to_equal(1)
expect(breaks_of(s: s)).to_equal(1)
expect(armed_of(s: s)).to_equal(true)
```

</details>

#### propagates when the handle is carried inside a struct built in that frame

- propagates when the handle is carried inside a struct built in that frame
   - Expected: mutate(h: boxed.dp) is true
   - Expected: steps_of(s: s) equals `1`
   - Expected: breaks_of(s: s) equals `1`
   - Expected: armed_of(s: s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates when the handle is carried inside a struct built in that frame")
val s = DbgSession.new()
val boxed = Acq(ok: true, dp: acquire(s: s))
expect(mutate(h: boxed.dp)).to_equal(true)
expect(steps_of(s: s)).to_equal(1)
expect(breaks_of(s: s)).to_equal(1)
expect(armed_of(s: s)).to_equal(true)
```

</details>

#### propagates when the target field is read directly off the session

- propagates when the target field is read directly off the session
   - Expected: mutate(h: s.target) is true
   - Expected: steps_of(s: s) equals `1`
   - Expected: breaks_of(s: s) equals `1`
   - Expected: armed_of(s: s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates when the target field is read directly off the session")
val s = DbgSession.new()
expect(mutate(h: s.target)).to_equal(true)
expect(steps_of(s: s)).to_equal(1)
expect(breaks_of(s: s)).to_equal(1)
expect(armed_of(s: s)).to_equal(true)
```

</details>

### partial survival — each field kind pinned independently

#### does not lose an OWN ARRAY field mutation

- does not lose an OWN ARRAY field mutation
   - Expected: "acquire" equals `Some`
   - Expected: breaks_of(s: s) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not lose an OWN ARRAY field mutation")
val s = DbgSession.new()
match acquire(s: s):
    case Some(t):
        val ok = t.set_breakpoint(loc: 15)
        val ok2 = t.set_breakpoint(loc: 27)
    case None:
        expect("acquire").to_equal("Some")
expect(breaks_of(s: s)).to_equal(2)
```

</details>

#### does not lose an OWN BOOL field mutation

- does not lose an OWN BOOL field mutation
   - Expected: "acquire" equals `Some`
   - Expected: armed_of(s: s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not lose an OWN BOOL field mutation")
val s = DbgSession.new()
match acquire(s: s):
    case Some(t):
        t.profile_begin()
    case None:
        expect("acquire").to_equal("Some")
expect(armed_of(s: s)).to_equal(true)
```

</details>

#### does not lose an OWN SCALAR field mutation

- does not lose an OWN SCALAR field mutation
   - Expected: "acquire" equals `Some`
   - Expected: steps_of(s: s) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not lose an OWN SCALAR field mutation")
val s = DbgSession.new()
match acquire(s: s):
    case Some(t):
        t.step()
        t.step()
    case None:
        expect("acquire").to_equal("Some")
expect(steps_of(s: s)).to_equal(2)
```

</details>

#### gives two separately-acquired handles the same underlying target

- gives two separately-acquired handles the same underlying target
   - Expected: mutate(h: h1) is true
   - Expected: mutate(h: h2) is true
   - Expected: steps_of(s: s) equals `2`
   - Expected: breaks_of(s: s) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives two separately-acquired handles the same underlying target")
val s = DbgSession.new()
val h1 = acquire(s: s)
val h2 = acquire(s: s)
expect(mutate(h: h1)).to_equal(true)
expect(mutate(h: h2)).to_equal(true)
expect(steps_of(s: s)).to_equal(2)
expect(breaks_of(s: s)).to_equal(2)
```

</details>

#### keeps distinct sessions isolated

- keeps distinct sessions isolated
   - Expected: mutate(h: acquire(s: a)) is true
   - Expected: steps_of(s: a) equals `1`
   - Expected: steps_of(s: b) equals `0`
   - Expected: breaks_of(s: b) equals `0`
   - Expected: armed_of(s: b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps distinct sessions isolated")
val a = DbgSession.new()
val b = DbgSession.new()
expect(mutate(h: acquire(s: a))).to_equal(true)
expect(steps_of(s: a)).to_equal(1)
expect(steps_of(s: b)).to_equal(0)
expect(breaks_of(s: b)).to_equal(0)
expect(armed_of(s: b)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `dc20383249243fe598c75dcc1766e81d88c2e3a512ffc861417b1265f69a29b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc20383249243fe598c75dcc1766e81d88c2e3a512ffc861417b1265f69a29b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc20383249243fe598c75dcc1766e81d88c2e3a512ffc861417b1265f69a29b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/debug/capability_handle_aliasing_spec.spl
mirror: doc/06_spec/01_unit/lib/debug/capability_handle_aliasing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug/capability_handle_aliasing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug/capability_handle_aliasing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug/capability_handle_aliasing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/debug/capability_handle_aliasing_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates every field kind when acquired as a free fn tail expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/capability_handle_aliasing_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates when the handle is bound to a local in the session's own frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/capability_handle_aliasing_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates when the handle is carried inside a struct built in that frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
