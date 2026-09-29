# forbidden_io_checker_spec

> Purpose: Prove that forbidden-I/O acquisition entry point set.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# forbidden_io_checker_spec

Purpose: Prove that forbidden-I/O acquisition entry point set.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/forbidden_io_checker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that forbidden-I/O acquisition entry point set.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### forbidden-I/O acquisition entry point set

#### recognizes the lazy loader-level acquisition functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes the lazy loader-level acquisition functions
- Verify: recognizes the lazy loader-level acquisition functions
   - Expected: is_forbidden_io_acquire_fn("apk_load_facet") is true
   - Expected: is_forbidden_io_acquire_fn("apk_load_aspect_manual") is true
   - Expected: is_forbidden_io_acquire_fn("apk_activate_startup") is true
   - Expected: is_forbidden_io_acquire_fn("_apk_acquire_facet") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes the lazy loader-level acquisition functions")
step("Verify: recognizes the lazy loader-level acquisition functions")
# @req: REQ-COMPILER-SEMANTICS-001
expect(is_forbidden_io_acquire_fn("apk_load_facet")).to_equal(true)
expect(is_forbidden_io_acquire_fn("apk_load_aspect_manual")).to_equal(true)
expect(is_forbidden_io_acquire_fn("apk_activate_startup")).to_equal(true)
expect(is_forbidden_io_acquire_fn("_apk_acquire_facet")).to_equal(true)
```

</details>

#### does NOT flag apk_try_facet — its own contract states it never performs I/O

- does NOT flag apk_try_facet — its own contract states it never performs I/O
- Verify: does NOT flag apk_try_facet — its own contract states it never performs I/O
   - Expected: is_forbidden_io_acquire_fn("apk_try_facet") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does NOT flag apk_try_facet — its own contract states it never performs I/O")
step("Verify: does NOT flag apk_try_facet — its own contract states it never performs I/O")
expect(is_forbidden_io_acquire_fn("apk_try_facet")).to_equal(false)
```

</details>

### check_forbidden_io_violations — direct call

#### REJECTS: an interrupt-context function directly calling apk_load_facet

- REJECTS: an interrupt-context function directly calling apk_load_facet
- Verify: REJECTS: an interrupt-context function directly calling apk_load_facet
   - Expected: violations.len() equals `1`
   - Expected: violations[0].kind equals `ForbiddenIoViolationKind.DirectAcquire`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REJECTS: an interrupt-context function directly calling apk_load_facet")
step("Verify: REJECTS: an interrupt-context function directly calling apk_load_facet")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["apk_load_facet"])
val violations = check_forbidden_io_violations("isr_tick", m)
expect(violations.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(violations[0].kind).to_equal(ForbiddenIoViolationKind.DirectAcquire)
```

</details>

#### REJECTS: a @noalloc-context function directly calling apk_load_aspect_manual

- REJECTS: a @noalloc-context function directly calling apk_load_aspect_manual
- Verify: REJECTS: a @noalloc-context function directly calling apk_load_aspect_manual
   - Expected: check_forbidden_io_violations("noalloc_step", m).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REJECTS: a @noalloc-context function directly calling apk_load_aspect_manual")
step("Verify: REJECTS: a @noalloc-context function directly calling apk_load_aspect_manual")
val m = ForbiddenIoContextManifest.new()
m.register("noalloc_step", false, false, true)
m.set_callees("noalloc_step", ["apk_load_aspect_manual"])
expect(check_forbidden_io_violations("noalloc_step", m).len()).to_equal(1)
```

</details>

#### REJECTS: a real-time-context function directly calling apk_activate_startup

- REJECTS: a real-time-context function directly calling apk_activate_startup
- Verify: REJECTS: a real-time-context function directly calling apk_activate_startup
   - Expected: check_forbidden_io_violations("rt_loop", m).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REJECTS: a real-time-context function directly calling apk_activate_startup")
step("Verify: REJECTS: a real-time-context function directly calling apk_activate_startup")
val m = ForbiddenIoContextManifest.new()
m.register("rt_loop", true, false, false)
m.set_callees("rt_loop", ["apk_activate_startup"])
expect(check_forbidden_io_violations("rt_loop", m).len()).to_equal(1)
```

</details>

#### PASSES: an interrupt-context function calling apk_try_facet (no I/O, legitimate)

- PASSES: an interrupt-context function calling apk_try_facet (no I/O, legitimate)
- Verify: PASSES: an interrupt-context function calling apk_try_facet (no I/O, legitimate)
   - Expected: check_forbidden_io_violations("isr_tick", m).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PASSES: an interrupt-context function calling apk_try_facet (no I/O, legitimate)")
step("Verify: PASSES: an interrupt-context function calling apk_try_facet (no I/O, legitimate)")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["apk_try_facet"])
expect(check_forbidden_io_violations("isr_tick", m).len()).to_equal(0)
```

</details>

#### PASSES: an ordinary (untagged) function calling apk_load_facet — not a forbidden context at all

- PASSES: an ordinary (untagged) function calling apk_load_facet — not a forbidden context at all
- Verify: PASSES: an ordinary (untagged) function calling apk_load_facet — not a forbidden context at all
   - Expected: check_forbidden_io_violations("ordinary_startup_fn", m).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PASSES: an ordinary (untagged) function calling apk_load_facet — not a forbidden context at all")
step("Verify: PASSES: an ordinary (untagged) function calling apk_load_facet — not a forbidden context at all")
val m = ForbiddenIoContextManifest.new()
m.register("ordinary_startup_fn", false, false, false)
m.set_callees("ordinary_startup_fn", ["apk_load_facet"])
expect(check_forbidden_io_violations("ordinary_startup_fn", m).len()).to_equal(0)
```

</details>

### check_forbidden_io_violations — transitive call

#### REJECTS: an interrupt-context function reaching apk_load_facet through two hops

- REJECTS: an interrupt-context function reaching apk_load_facet through two hops
- Verify: REJECTS: an interrupt-context function reaching apk_load_facet through two hops
   - Expected: violations.len() equals `1`
   - Expected: violations[0].kind equals `ForbiddenIoViolationKind.TransitiveAcquire`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REJECTS: an interrupt-context function reaching apk_load_facet through two hops")
step("Verify: REJECTS: an interrupt-context function reaching apk_load_facet through two hops")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["helper_a"])
m.set_callees("helper_a", ["helper_b"])
m.set_callees("helper_b", ["apk_load_facet"])
val violations = check_forbidden_io_violations("isr_tick", m)
expect(violations.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(violations[0].kind).to_equal(ForbiddenIoViolationKind.TransitiveAcquire)
```

</details>

#### PASSES: an interrupt-context function whose transitive chain never reaches an acquisition fn

- PASSES: an interrupt-context function whose transitive chain never reaches an acquisition fn
- Verify: PASSES: an interrupt-context function whose transitive chain never reaches an acquisition fn
   - Expected: check_forbidden_io_violations("isr_tick", m).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PASSES: an interrupt-context function whose transitive chain never reaches an acquisition fn")
step("Verify: PASSES: an interrupt-context function whose transitive chain never reaches an acquisition fn")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["helper_a"])
m.set_callees("helper_a", ["helper_b"])
m.set_callees("helper_b", ["apk_try_facet"])
expect(check_forbidden_io_violations("isr_tick", m).len()).to_equal(0)
```

</details>

#### does not hang on a call-graph cycle that never reaches an acquisition fn

- does not hang on a call-graph cycle that never reaches an acquisition fn
- Verify: does not hang on a call-graph cycle that never reaches an acquisition fn
   - Expected: check_forbidden_io_violations("isr_tick", m).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not hang on a call-graph cycle that never reaches an acquisition fn")
step("Verify: does not hang on a call-graph cycle that never reaches an acquisition fn")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["helper_a"])
m.set_callees("helper_a", ["helper_b"])
m.set_callees("helper_b", ["helper_a"])
expect(check_forbidden_io_violations("isr_tick", m).len()).to_equal(0)
```

</details>

### check_all_forbidden_io_fns — bulk

#### collects violations only from tagged functions, across a mixed manifest

- collects violations only from tagged functions, across a mixed manifest
- Verify: collects violations only from tagged functions, across a mixed manifest
   - Expected: violations.len() equals `1`
   - Expected: violations[0].fn_name equals `isr_tick`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects violations only from tagged functions, across a mixed manifest")
step("Verify: collects violations only from tagged functions, across a mixed manifest")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["apk_load_facet"])
m.register("plain_startup_fn", false, false, false)
m.set_callees("plain_startup_fn", ["apk_load_facet"])
m.register("rt_publisher", true, false, false)
m.set_callees("rt_publisher", ["apk_try_facet"])
val violations = check_all_forbidden_io_fns(m)
expect(violations.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(violations[0].fn_name).to_equal("isr_tick")
```

</details>

### DEFECT-CLASS NEGATIVE — the check, not something else, is what rejects

#### removing the context tag (is_interrupt/is_realtime/is_noalloc all false) makes the identical call \

- collects violations only from tagged functions, across a mixed manifest
   - Expected: check_forbidden_io_violations("was_isr_tick", m).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects violations only from tagged functions, across a mixed manifest")
graph PASS — proves the violations above come from the context tag + acquisition-fn match, not from \
some other coincidental property of the fixture":
val m = ForbiddenIoContextManifest.new()
m.register("was_isr_tick", false, false, false)
m.set_callees("was_isr_tick", ["apk_load_facet"])
expect(check_forbidden_io_violations("was_isr_tick", m).len()).to_equal(0)
```

</details>

### diagnostic formatting

#### carries the E-APACK008 code

- carries the E-APACK008 code
- Verify: carries the E-APACK008 code
   - Expected: messages.len() equals `1`
   - Expected: messages[0].starts_with("error[E-APACK008]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the E-APACK008 code")
step("Verify: carries the E-APACK008 code")
val m = ForbiddenIoContextManifest.new()
m.register("isr_tick", false, true, false)
m.set_callees("isr_tick", ["apk_load_facet"])
val messages = format_forbidden_io_violations(check_forbidden_io_violations("isr_tick", m))
expect(messages.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(messages[0].starts_with("error[E-APACK008]")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `50dfe471b9f0e2c5324810faaa6bd1c5f77082802c429b9efd69de7e8f9fed08`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50dfe471b9f0e2c5324810faaa6bd1c5f77082802c429b9efd69de7e8f9fed08`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50dfe471b9f0e2c5324810faaa6bd1c5f77082802c429b9efd69de7e8f9fed08`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/forbidden_io_checker_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/forbidden_io_checker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/forbidden_io_checker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/forbidden_io_checker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/forbidden_io_checker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/forbidden_io_checker_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes the lazy loader-level acquisition functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/forbidden_io_checker_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT flag apk_try_facet — its own contract states it never performs I/O' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/forbidden_io_checker_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REJECTS: an interrupt-context function directly calling apk_load_facet' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
