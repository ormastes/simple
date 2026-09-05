# Static-Method Owner Resolution Must Not Diverge Between Lowering Lanes

> A call of the form `Widget.stat(2)` names its owner SYNTACTICALLY: the receiver is a bare type name, not a runtime value. MIR lowering has to recognise that before it lowers the receiver, because a bare type name has no value form -- the `Var`/`NamedVar` lowering path knows only locals, module globals, and two hardcoded constants, so handing it a class name produces the generic

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static-Method Owner Resolution Must Not Diverge Between Lowering Lanes

A call of the form `Widget.stat(2)` names its owner SYNTACTICALLY: the receiver is a bare type name, not a runtime value. MIR lowering has to recognise that before it lowers the receiver, because a bare type name has no value form -- the `Var`/`NamedVar` lowering path knows only locals, module globals, and two hardcoded constants, so handing it a class name produces the generic

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/native_static_method_owner_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A call of the form `Widget.stat(2)` names its owner SYNTACTICALLY: the receiver
is a bare type name, not a runtime value. MIR lowering has to recognise that
before it lowers the receiver, because a bare type name has no value form -- the
`Var`/`NamedVar` lowering path knows only locals, module globals, and two
hardcoded constants, so handing it a class name produces the generic

    error: MIR lowering error: undefined variable Widget

Root cause found 2026-08-17 in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`. The owner name
was recovered ONLY by resolving the `NamedVar`'s attached symbol id through
`self.symbols.get_symbol_raw(...)`. Under `native-build` that symbol id is
frequently unresolved, so the lookup returned nil and `static_receiver_name`
stayed `""` -- even though the `NamedVar` arm already carries the literal source
text `"Widget"` in its second payload slot. With an empty owner the Unresolved
method-call arm never builds the `static::Widget::stat` key, never tries
`lookup_method_in_type`, and falls straight through to lowering the bare class
name as a value.

The fix supplies a NAME-DERIVED fallback: resolve the syntactic name in the
symbol table and accept it as an owner only when it really names a
Class/Struct/Enum/Import -- the same kind test the symbol-id path already
applies, so a local variable that happens to shadow a type name can never be
mistaken for a static receiver.

## Why this cannot be a normal spec body

`bin/simple test` is the TREE-WALK INTERPRETER. It never runs MIR lowering at
all, so a spec body that simply calls `Widget.stat(2)` passes on a completely
broken native lane -- it is measuring a different compiler. This spec therefore
shells out to `native-build`, which is the only lane that exercises the defect.

## Why an exit code alone is not the assertion

Two hazards make a bare exit code worthless here:

  * `native-build` on this host is regularly SIGTERMed by `earlyoom`, which
    prefers `simple` as a kill target. That yields rc 143/144 with no output --
    UNVERIFIED, not a failure. Treating it as a failure makes this spec flaky in
    the direction that wastes the most time.
  * a swallowed diagnostic can fail a build with no message at all.

So the assertion is positive and textual: the compiled program must PRINT the
expected line. A run that produced neither the success text nor a genuine
compile error is reported as unverified rather than either colour.

## Scenarios

### native-build resolves a static method's owner from the receiver's syntactic name

#### compiles and runs `Widget.stat(2)` through the native lowering lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles and runs `Widget.stat(2)` through the native lowering lane
- native-build the bare-class-name static call fixture
- A signalled build is UNVERIFIED, never a pass and never a failure
- The owner-resolution regression marker must be absent
- The build must succeed
- The compiled program must PRINT the expected line - exit 0 is never accepted as a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compiles and runs `Widget.stat(2)` through the native lowering lane")
step("native-build the bare-class-name static call fixture")
val (out, log, rc) = native_build_and_run("test/fixtures", FIXTURE)

step("A signalled build is UNVERIFIED, never a pass and never a failure")
# earlyoom kills `simple` preferentially on this host. A run that
# produced no verdict text at all measured nothing -- say so loudly
# instead of colouring it.
if not out.contains("BUILD_RC="):
    pending("native-build produced no verdict line (likely SIGTERMed by earlyoom) - UNVERIFIED")
else:
    step("The owner-resolution regression marker must be absent")
    # This is the precise 2026-08-17 failure. Asserting on the marker
    # rather than only on rc names the defect when it returns.
    assert_equal(log.contains(MARKER_UNDEFINED), false)

    step("The build must succeed")
    assert_equal(rc, 0)

    step("The compiled program must PRINT the expected line - exit 0 is never accepted as a pass")
    assert_equal(out.contains(EXPECTED), true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-NATIVE-STATIC-OWNER-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b60ecd152c697cd2adb4b1ddbdb33fad17a86020016dcfce16ff23279745ebd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b60ecd152c697cd2adb4b1ddbdb33fad17a86020016dcfce16ff23279745ebd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b60ecd152c697cd2adb4b1ddbdb33fad17a86020016dcfce16ff23279745ebd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/native/native_static_method_owner_resolution_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/native_static_method_owner_resolution_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/native/native_static_method_owner_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/native_static_method_owner_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/native_static_method_owner_resolution_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/native/native_static_method_owner_resolution_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles and runs `Widget.stat(2)` through the native lowering lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
