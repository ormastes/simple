# Optional unwrap (`!`) on variables, member chains, and call arguments

> Anyone writing Simple code that stores an optional (`i64?`, `text?`) in a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optional unwrap (`!`) on variables, member chains, and call arguments

Anyone writing Simple code that stores an optional (`i64?`, `text?`) in a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | Implemented (interpreter) / DEFECTIVE (JIT) |
| Source | `test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Anyone writing Simple code that stores an optional (`i64?`, `text?`) in a
variable and later unwraps it with `!`. This spec pins the values that unwrap
must produce, so the closure of
`doc/08_tracking/bug/interpreter_bang_unwrap_member_access_2026-05-08.md`
stops being evidence-free.

## Scope and Preconditions

`bin/simple test` executes specs on the tree-walk INTERPRETER, which is the
engine this file can assert against. The same expressions are corrupt on the
Cranelift JIT that `bin/simple run` uses — see
`doc/08_tracking/bug/jit_optional_i64_payload_reinterpreted_2026-08-17.md`.
This spec therefore proves the interpreter half only, and deliberately says so
rather than implying whole-language coverage.

## Primary Workflow

An optional is bound, inspected, unwrapped with `!`, and nil-coalesced. Each
step asserts the exact payload value, never merely that the expression parsed.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `!` unwrap | Yields the payload of a non-nil optional |
| `??` coalesce | Yields the payload when non-nil, the default only on nil |

## Related Specifications

- `doc/08_tracking/bug/interpreter_bang_unwrap_member_access_2026-05-08.md` — the closure this covers

## Scenarios

### Optional unwrap with the ! operator

#### yields the stored payload when unwrapping a variable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- yields the stored payload when unwrapping a variable
- Bind an i64 optional to a known value
- Read the optional without unwrapping
   - Expected: x.to_string() equals `42`
- Unwrap the variable with !
   - Expected: x! equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("yields the stored payload when unwrapping a variable")
step("Bind an i64 optional to a known value")
val x: i64? = 42

step("Read the optional without unwrapping")
# The original defect rendered this as a denormal float, so assert the
# exact integer text rather than merely that it is non-empty.
expect(x.to_string()).to_equal("42")

step("Unwrap the variable with !")
expect(x!).to_equal(42)
```

</details>

#### yields the payload of an optional returned from a function

- yields the payload of an optional returned from a function
- Call a function declared to return i64?
- The value renders as its integer payload, not a raw handle
   - Expected: g.to_string() equals `7`
- Unwrapping it produces the payload
   - Expected: g! equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("yields the payload of an optional returned from a function")
step("Call a function declared to return i64?")
val g = give_int()

step("The value renders as its integer payload, not a raw handle")
expect(g.to_string()).to_equal("7")

step("Unwrapping it produces the payload")
expect(g!).to_equal(7)
```

</details>

#### unwraps a text optional to its exact contents

- unwraps a text optional to its exact contents
- Call a function declared to return text?
- Unwrapping yields the original string
   - Expected: t! equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps a text optional to its exact contents")
step("Call a function declared to return text?")
val t = give_text()

step("Unwrapping yields the original string")
expect(t!).to_equal("ok")
```

</details>

#### returns the payload from ?? and the default only on nil

- returns the payload from ?? and the default only on nil
- Coalesce a present optional -- the default must NOT be taken
   - Expected: x ?? 99 equals `42`
- Coalesce an absent optional -- the default IS taken
   - Expected: n ?? 99 equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the payload from ?? and the default only on nil")
step("Coalesce a present optional -- the default must NOT be taken")
val x: i64? = 42
expect(x ?? 99).to_equal(42)

step("Coalesce an absent optional -- the default IS taken")
val n = give_nil()
expect(n ?? 99).to_equal(99)
```

</details>

#### treats an absent optional as nil

- treats an absent optional as nil
- A function returning nil produces a nil optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats an absent optional as nil")
step("A function returning nil produces a nil optional")
val n = give_nil()
expect(n).to_be_nil()
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

- `REQ-SSPEC-UNIT`
- `REQ-LANG-OPTIONAL-UNWRAP-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `920a5b4283266a97e9e057d9240b0e13a4473b412fe3b1b5a20603cb3a151f17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `920a5b4283266a97e9e057d9240b0e13a4473b412fe3b1b5a20603cb3a151f17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `920a5b4283266a97e9e057d9240b0e13a4473b412fe3b1b5a20603cb3a151f17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/optional_unwrap_bang_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter/optional_unwrap_bang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/optional_unwrap_bang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields the stored payload when unwrapping a variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields the payload of an optional returned from a function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps a text optional to its exact contents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
