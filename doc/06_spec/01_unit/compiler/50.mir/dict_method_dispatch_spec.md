# Dict method dispatch must never fall through to a `str.*` implementation

> MIR lowering decides whether a method call on a receiver is a *Dict* method via an allow-list, `is_dict_method_name` (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`). A method missing from that list never reaches the dict dispatch arms and instead falls through to a same-named implementation on another type -- in practice the `str.*` one, whose runtime guard (`src/runtime/runtime_native.c:7873`) refuses a non-text receiver and aborts:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict method dispatch must never fall through to a `str.*` implementation

MIR lowering decides whether a method call on a receiver is a *Dict* method via an allow-list, `is_dict_method_name` (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`). A method missing from that list never reaches the dict dispatch arms and instead falls through to a same-named implementation on another type -- in practice the `str.*` one, whose runtime guard (`src/runtime/runtime_native.c:7873`) refuses a non-text receiver and aborts:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/dict_method_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

MIR lowering decides whether a method call on a receiver is a *Dict* method
via an allow-list, `is_dict_method_name`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`). A method
missing from that list never reaches the dict dispatch arms and instead falls
through to a same-named implementation on another type -- in practice the
`str.*` one, whose runtime guard (`src/runtime/runtime_native.c:7873`)
refuses a non-text receiver and aborts:

    Runtime error: str.clear was called on a receiver that is not text.
    This method has no compiled implementation for that receiver type --
    a code-generation dispatch gap, not a program error.

`.clear()` was missing, which is the defect this spec reproduces. `.set()`
was missing before it (`doc/08_tracking/bug/dict_set_bracket_write_parity_2026-08-07.md`),
so this is a recurring CLASS, not an instance -- hence the second, sweeping
example below.

## Why `.clear()` mattered far beyond a missing method

`HirLowering.begin_module()` (`src/compiler/20.hir/hir_lowering/types.spl:283`)
is the per-module reset run once per source file
(`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:244`), and it is
built out of **15 `Dict.clear()` calls** -- including
`materialized_payload_bindings.clear()` and `SymbolTable.reset_module()`'s own
8 dict clears. Those clears did not happen, while the *scalar* resets on the
following lines (`next_symbol_id = 0`, `next_scope_id = 1`) did. So symbol
NAMES from previously-lowered modules survived while symbol IDS restarted at
0, and each new module silently overwrote ids that stale names still pointed
at -- making a type-name lookup return the id of an unrelated function from
another module.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `is_dict_method_name` | Allow-list gating the Dict dispatch arms; omission = silent fall-through |
| `rt_dict_clear` | Runtime impl (runtime_native.c:8167), declared at llvm_lib_translate.spl:447 |
| Mis-dispatch signature | `str.<m> was called on a receiver that is not text` + non-zero exit |

## Related Specifications

- doc/08_tracking/bug/dict_set_bracket_write_parity_2026-08-07.md — the prior `.set()` instance of this class

## Scenarios

### Dict method dispatch never falls through to a str.* implementation

#### routes Dict.clear() to rt_dict_clear and empties the dict

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes Dict.clear() to rt_dict_clear and empties the dict
- Run the Dict.clear() fixture in a child process
- Confirm the child ran: clean exit and non-empty stdout
- Confirm it did not mis-dispatch to the string implementation
- Confirm clear() actually emptied the dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes Dict.clear() to rt_dict_clear and empties the dict")
step("Run the Dict.clear() fixture in a child process")
val (out, err, code) = run_method("clear")

# Non-vacuity first: prove the child actually RAN and produced output
# before asserting anything about its content. A content-only
# assertion cannot distinguish "ran wrong" from "did not run".
step("Confirm the child ran: clean exit and non-empty stdout")
assert_equal(code, 0)
assert_equal(out.trim() == "", false)

step("Confirm it did not mis-dispatch to the string implementation")
assert_equal(out.contains("str.clear was called on a receiver that is not text"), false)
assert_equal(err.contains("str.clear was called on a receiver that is not text"), false)
assert_equal(err.contains("code-generation dispatch gap"), false)

step("Confirm clear() actually emptied the dict")
assert_equal(out.contains("method=clear ok=1 len=0"), true)
```

</details>

#### dispatches every method on the Dict surface without a str.*/array.* fall-through

- dispatches every method on the Dict surface without a str.*/array.* fall-through
- Run one child process per Dict method and collect the failures
- Confirm the sweep was not vacuous: every method was actually exercised
- Confirm no Dict method mis-dispatched


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches every method on the Dict surface without a str.*/array.* fall-through")
step("Run one child process per Dict method and collect the failures")
var failures: [text] = []
var ran = 0

for method in DICT_METHODS:
    val (out, err, code) = run_method(method)
    val combined = out + "\n" + err

    # Non-vacuity per method: a method that produced no output at all
    # is a failure, not a pass.
    if code != 0 or out.trim() == "":
        failures = failures.push("{method}: child did not run cleanly (rc={code})")
    elif combined.contains("code-generation dispatch gap"):
        failures = failures.push("{method}: mis-dispatched -- dispatch gap reported")
    elif combined.contains("was called on a receiver that is not"):
        failures = failures.push("{method}: mis-dispatched to a foreign receiver impl")
    elif not out.contains("method={method} ok=1"):
        failures = failures.push("{method}: fixture did not report success")
    else:
        ran = ran + 1

step("Confirm the sweep was not vacuous: every method was actually exercised")
assert_equal(ran + failures.len(), DICT_METHODS.len())
assert_equal(DICT_METHODS.len() > 0, true)

step("Confirm no Dict method mis-dispatched")
assert_equal(failures.len(), 0)
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
- `REQ-MIR-DICT-DISPATCH-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e16a593cfea2171abe23f9d5b6dd54b23042f188f87044b4581ca028b35604b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e16a593cfea2171abe23f9d5b6dd54b23042f188f87044b4581ca028b35604b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e16a593cfea2171abe23f9d5b6dd54b23042f188f87044b4581ca028b35604b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/50.mir/dict_method_dispatch_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/dict_method_dispatch_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/50.mir/dict_method_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/dict_method_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/dict_method_dispatch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/50.mir/dict_method_dispatch_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes Dict.clear() to rt_dict_clear and empties the dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/dict_method_dispatch_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches every method on the Dict surface without a str.*/array.* fall-through' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
