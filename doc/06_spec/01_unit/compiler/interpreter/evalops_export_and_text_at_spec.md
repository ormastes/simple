# Evalops Export And Text At Specification

> Tests covering interpreter _EvalOps exports and text.at.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Evalops Export And Text At Specification

## Scenarios

### interpreter _EvalOps exports and text.at

#### exports every _EvalOps function from the package __init__

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports every _EvalOps function from the package __init__
   - Expected: unexported_fns(call_src, init_src) equals ``
   - Expected: unexported_fns(access_src, init_src) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports every _EvalOps function from the package __init__")
# THE ITEM-3 PIN, and the reason items 1 and 2 stayed hidden for so long.
#
# eval_ops.spl re-exports the package with
# `export use ..._EvalOps.*`, so a new helper is automatically visible
# to importers of eval_ops. But __init__.spl -- what
# `use compiler.frontend.core.interpreter.*` resolves -- uses EXPLICIT
# export lists and does NOT inherit that wildcard. A function added to
# _EvalOps is therefore invisible to every out-of-tree importer until
# somebody remembers to list it, and the failure surfaces as a link
# error in an unrelated file, far from the edit that caused it.
#
# Mechanical rather than a hand-written name list: adding a `fn` to
# _EvalOps without exporting it turns this red and NAMES the function.
val init_src = read_src(INIT_PATH)
expect(init_src.len()).to_be_greater_than(0)
val call_src = read_src(CALL_METHOD_PATH)
expect(call_src.len()).to_be_greater_than(0)
val access_src = read_src(ACCESS_PATH)
expect(access_src.len()).to_be_greater_than(0)

# Self-check first: the scanner must actually find functions. Without
# this, a scanner that silently matched nothing would report "no gaps"
# and be vacuously green -- the false-green shape this campaign keeps
# hitting.
expect(unexported_fns(call_src, "")).to_contain("eval_int_method")
expect(unexported_fns(access_src, "")).to_contain("eval_text_method")

expect(unexported_fns(call_src, init_src)).to_equal("")
expect(unexported_fns(access_src, init_src)).to_equal("")
```

</details>

#### keeps eval_int_method reachable from the package export list

- keeps eval_int_method reachable from the package export list


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps eval_int_method reachable from the package export list")
# THE ITEM-1 PIN, stated as the specific symbol rather than relying on
# the generic scan above, because this one has a live call site:
# _EvalOps/call_method_eval.spl dispatches VAL_INT receivers to it. An
# importer that reached core_interpret_expr therefore died on
# `(42).to_text()` before evaluating anything.
val call_src = read_src(CALL_METHOD_PATH)
expect(call_src).to_contain("return eval_int_method(receiver, method_name, arg_eids)")
expect(call_src).to_contain("fn eval_int_method(")

val init_src = read_src(INIT_PATH)
expect(init_src).to_contain("export eval_int_method")
```

</details>

#### routes each receiver kind to a dispatcher the package exports

- routes each receiver kind to a dispatcher the package exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes each receiver kind to a dispatcher the package exports")
# Generalises the block above: every `eval_*_method` the per-kind
# dispatch calls must be exported, not just the one that bit us.
val init_src = read_src(INIT_PATH)
expect(init_src).to_contain(" eval_array_method")
expect(init_src).to_contain(" eval_text_method")
expect(init_src).to_contain(" eval_int_method")
```

</details>

#### gives text an at arm in the LIVE dispatch table

- gives text an at arm in the LIVE dispatch table


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives text an at arm in the LIVE dispatch table")
# THE ITEM-2 PIN. `at` was absent from the live text table AND from the
# eval_methods.spl copy deleted on 2026-08-01, so it is a genuine gap
# rather than a regression from that deletion. Arrays already had `at`.
#
# This asserts against the file that ACTUALLY RUNS. The sole call site
# of eval_text_method is _EvalOps/call_method_eval.spl, in this same
# _EvalOps package, so the package-local definition is the one that
# resolves -- proven by two-directional sabotage through
# core_interpret_expr in
# doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md
val access_src = read_src(ACCESS_PATH)
expect(access_src).to_contain("if method_name == \"at\":")

val body = arm_body(access_src, "if method_name == \"at\":", "if method_name == \"parse_int\":")
expect(body.len()).to_be_greater_than(0)
# In range: a one-byte slice, the same shape char_at uses.
expect(body).to_contain("s.substring(at_idx, at_idx + 1)")
# Bounds-checked on both ends, negative index included.
expect(body).to_contain("at_idx >= 0 and at_idx < s.len()")
```

</details>

#### returns flat None from text .at out of range, matching array .at

- returns flat None from text .at out of range, matching array .at


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns flat None from text .at out of range, matching array .at")
# `.at` is this codebase's bounds-checked Option accessor. Array `.at`
# returns flat-None (nil) past the end -- the element itself is its own
# `Some`, per the FLAT Option encoding; there is no VAL_ENUM in this
# interpreter. 250+ call sites `match x.at(i)` as Some/None, so a text
# `.at` returning "" would make every one of them take the Some branch
# on an out-of-range read.
#
# The two receivers are asserted side by side so they cannot drift apart
# silently the way `at` itself did.
val access_src = read_src(ACCESS_PATH)
val text_at = arm_body(access_src, "if method_name == \"at\":", "if method_name == \"parse_int\":")
expect(text_at).to_contain("return val_make_nil()")
# ...and NOT the seed's empty-string convention.
expect(text_at).to_not_contain("val_make_text(\"\")")

val call_src = read_src(CALL_METHOD_PATH)
val array_at = arm_body(call_src, "if method_name == \"at\":", "if method_name == \"map\":")
expect(array_at).to_contain("return val_make_nil()")
```

</details>

#### fails LOUDLY when text .at is called with no index

- fails LOUDLY when text .at is called with no index


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails LOUDLY when text .at is called with no index")
# A missing argument is a caller bug, not an empty string. char_at's
# older no-arg behaviour (return "") is exactly the silent-default shape
# this campaign keeps having to undo, so `at` must not copy it.
val access_src = read_src(ACCESS_PATH)
val body = arm_body(access_src, "if method_name == \"at\":", "if method_name == \"parse_int\":")
expect(body).to_contain("eval_set_error(\"at() requires an index argument\")")
expect(body).to_contain("return -1")
```

</details>

#### documents text .at as a deliberate divergence from the seed

- documents text .at as a deliberate divergence from the seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents text .at as a deliberate divergence from the seed")
# DO NOT "fix" this toward the seed. The seed
# (src/compiler_rust/compiler/src/interpreter_method/string.rs, where
# `"char_at" | "at"` share one arm) is CHARACTER-indexed and returns ""
# out of range. The C runtime's rt_string_char_at -- what `s[i]` lowers
# to on native/JIT via rt_index_get -- is a raw one-byte slice returning
# nil out of range. This interpreter matches the RUNTIME on both axes,
# because interpreter/native agreement is the property that matters for
# a compiler lane, and because len/index_of/slice/char_at here all hand
# out byte offsets so a character-indexed `at` would not compose with
# them. Same reasoning already recorded on char_at.
#
# Pinning the comment, not just the code, because the next person to
# diff the interpreter against the seed will otherwise "fix" the
# divergence and silently break the composition property.
val access_src = read_src(ACCESS_PATH)
val body = arm_body(access_src, "# Text `at`:", "if method_name == \"parse_int\":")
expect(body).to_contain("rt_string_char_at")
expect(body).to_contain("interpreter_method/string.rs")
expect(body).to_contain("bounds-checked Option accessor")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter _EvalOps exports and text.at.
- interpreter _EvalOps exports and text.at

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b0cb9d0b65fe2e7387443c0656a7b87684f36b2be7f05470a810bfb0d1c7e70c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0cb9d0b65fe2e7387443c0656a7b87684f36b2be7f05470a810bfb0d1c7e70c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0cb9d0b65fe2e7387443c0656a7b87684f36b2be7f05470a810bfb0d1c7e70c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports every _EvalOps function from the package __init__' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps eval_int_method reachable from the package export list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes each receiver kind to a dispatcher the package exports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
