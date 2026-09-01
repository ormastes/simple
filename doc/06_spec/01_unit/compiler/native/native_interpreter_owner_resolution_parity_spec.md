# Similar-Problem Detection: Owner/Static Resolution Parity Across Lowering Lanes

> This is a CLASS detector, not a single-bug regression test. Its sibling (`native_static_method_owner_resolution_spec.spl`) pins one instance -- `Widget.stat(2)` reported as `undefined variable Widget` under `native-build`. This spec exists because that instance is the third of its kind, and the previous two were each fixed narrowly and then recurred in a different shape:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Similar-Problem Detection: Owner/Static Resolution Parity Across Lowering Lanes

This is a CLASS detector, not a single-bug regression test. Its sibling (`native_static_method_owner_resolution_spec.spl`) pins one instance -- `Widget.stat(2)` reported as `undefined variable Widget` under `native-build`. This spec exists because that instance is the third of its kind, and the previous two were each fixed narrowly and then recurred in a different shape:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is a CLASS detector, not a single-bug regression test. Its sibling
(`native_static_method_owner_resolution_spec.spl`) pins one instance --
`Widget.stat(2)` reported as `undefined variable Widget` under `native-build`.
This spec exists because that instance is the third of its kind, and the
previous two were each fixed narrowly and then recurred in a different shape:

  * `File.delete(path)` -> `undefined variable: File`
    (native_build_mir_lowering_undefined_file_symbol_2026-08-08) -- fixed by
    skipping a Dict-name-collision probe for known class receivers.
  * `Widget.stat(2)` -> `undefined variable Widget` (2026-08-17) -- fixed by
    deriving the owner from the receiver's syntactic name when its symbol id is
    unresolved.

The invariant behind all of them is one sentence: **a method call's owner must
resolve to the same thing regardless of which engine lowers it.** Whenever the
native lane loses an owner the interpreter keeps, the symptom is a bare type or
receiver name escaping into value-lowering and surfacing as `undefined
variable <Name>`.

## Method: differential, not absolute

The interpreter is the ORACLE. For each call shape, the same fixture is executed
twice -- once through `SIMPLE_EXECUTION_MODE=interpreter` (`run`, tree-walk) and
once through `native-build` (AOT MIR lowering + codegen). The assertion is that
the two AGREE on stdout.

This is deliberately not a table of expected strings. A hardcoded expectation
tells you a lane broke but not that the lanes DIVERGED, and it silently rots
when the fixture is edited. Comparing lanes means a future call shape added to
the fixture is covered without touching this file.

## Why `bin/simple test` cannot host the measurement

`test` is the tree-walk interpreter and `run` is the Cranelift JIT; neither runs
the AOT native pipeline. A spec BODY therefore cannot observe a native-only
defect at all -- it would be measuring the oracle against itself. Every arm here
shells out.

## Hazards this spec is built around

  * **Signals are not failures.** `earlyoom` on this host is configured to
    prefer `simple` as a kill target, so a build can die with rc 143/144 and no
    output. That is UNVERIFIED. Colouring it red trains people to ignore this
    spec; colouring it green defeats the point. It is reported as pending.
  * **Exit 0 is never a pass.** Both lanes must emit non-empty stdout before any
    comparison is meaningful; a runner has been observed exiting 0 having
    printed nothing but warnings.
  * **rc is never read through a pipe.** A pipeline's `$?` belongs to its last
    stage.
  * **Silent interpreter demotion.** One unsupported operation demotes a whole
    program off the native lane, which would make a native defect vanish and this
    spec pass vacuously. The fixtures are kept minimal and single-purpose so
    there is nothing to trip that demotion.

## Scenarios

<details>
<summary>Advanced: native-build produced no verdict line (likely SIGTERMed by earlyoom) - UNVERIFIED</summary>

#### native-build produced no verdict line (likely SIGTERMed by earlyoom) - UNVERIFIED _(pending)_

</details>

### owner and static-method resolution agree between the native and interpreter lowering lanes

#### agrees on a bare-class-name static call (`Widget.stat(2)`)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- agrees on a bare-class-name static call (`Widget.stat(2)`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees on a bare-class-name static call (`Widget.stat(2)`)")
# Instance shape of the 2026-08-17 defect.
check_parity("test/fixtures", FIXTURE_STATIC)
```

</details>

#### agrees on the mixed free/cross-module/instance/static/trait call fixture

- agrees on the mixed free/cross-module/instance/static/trait call fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees on the mixed free/cross-module/instance/static/trait call fixture")
# The broadest owner-resolution fixture in the tree: same-module and
# cross-module free functions, an instance method, a STATIC method, and a
# trait-typed receiver. It is also what
# scripts/check/check-native-trailing-default-param.shs drives, so a
# divergence here and a red pre-push guard can never disagree silently.
check_parity("test/fixtures", FIXTURE_TRAILING)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-NATIVE-OWNER-PARITY-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a16e6052fc4ada7884b3bca52d4bbd9aaeb59f5a5c1f60dd51641cc83ec95a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a16e6052fc4ada7884b3bca52d4bbd9aaeb59f5a5c1f60dd51641cc83ec95a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a16e6052fc4ada7884b3bca52d4bbd9aaeb59f5a5c1f60dd51641cc83ec95a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on a bare-class-name static call (`Widget.stat(2)`)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on the mixed free/cross-module/instance/static/trait call fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
