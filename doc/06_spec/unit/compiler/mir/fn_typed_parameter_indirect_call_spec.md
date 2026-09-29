# Fn Typed Parameter Indirect Call Specification

> Tests covering fn-typed parameter call MIR lowering, fn reference constant LLVM emission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fn Typed Parameter Indirect Call Specification

## Scenarios

### fn-typed parameter call MIR lowering

#### calls a fn-typed parameter indirectly, never as a direct symbol call to its name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls a fn-typed parameter indirectly, never as a direct symbol call to its name
   - Expected: count_indirect_calls(f) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a fn-typed parameter indirectly, never as a direct symbol call to its name")
val mir = lower_source(apply_source)
val apply_fn = find_function(mir, "apply")
assert_true(apply_fn.?)
val f = apply_fn.unwrap()
expect_not(has_direct_call_named(f, "f"))
# closure arm + raw-fn arm of the existing indirect-call diamond
expect(count_indirect_calls(f)).to_equal(2)
```

</details>

#### merges the indirect-call result through one slot, not a multi-def temp

- merges the indirect-call result through one slot, not a multi-def temp
   - Expected: stores equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges the indirect-call result through one slot, not a multi-def temp")
val mir = lower_source(apply_source)
val f = find_function(mir, "apply").unwrap()
assert_true(max_copy_dest_block_count(f) <= 1)
var saw_alloc = false
var saw_load = false
var stores = 0
for block in f.blocks:
    for instruction in block.instructions:
        match instruction.kind:
            case MirInstKind.Alloc(_, _):
                saw_alloc = true
            case MirInstKind.Store(_, _):
                stores = stores + 1
            case MirInstKind.Load(_, _):
                saw_load = true
            case _:
                pass
assert_true(saw_alloc)
expect(stores).to_equal(2)
assert_true(saw_load)
```

</details>

#### passes a named function as the argument, keeping the outer call direct

- passes a named function as the argument, keeping the outer call direct
   - Expected: count_indirect_calls(main_fn) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a named function as the argument, keeping the outer call direct")
val mir = lower_source(apply_source)
val main_fn = find_function(mir, "main").unwrap()
assert_true(has_direct_call_named(main_fn, "apply"))
expect(count_indirect_calls(main_fn)).to_equal(0)
```

</details>

#### calls a fn-typed local holding a named function indirectly

- calls a fn-typed local holding a named function indirectly
   - Expected: count_indirect_calls(run_fn) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a fn-typed local holding a named function indirectly")
val source = "fn double(v: i64) -> i64:\n    v * 2\n\nfn run() -> i64:\n    val g: fn(i64) -> i64 = double\n    g(4)\n"
val mir = lower_source(source)
val run_fn = find_function(mir, "run").unwrap()
expect_not(has_direct_call_named(run_fn, "g"))
expect(count_indirect_calls(run_fn)).to_equal(2)
```

</details>

#### keeps an ordinary top-level function call direct

- keeps an ordinary top-level function call direct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an ordinary top-level function call direct")
val mir = lower_source(apply_source)
val main_fn = find_function(mir, "main").unwrap()
assert_true(has_direct_call_named(main_fn, "apply"))
```

</details>

#### still inlines a val-bound lambda call instead of demoting it

- still inlines a val-bound lambda call instead of demoting it
   - Expected: count_indirect_calls(run_fn) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still inlines a val-bound lambda call instead of demoting it")
val source = "fn run() -> i64:\n    val inc = \\v: v + 1\n    inc(4)\n"
val mir = lower_source(source)
val run_fn = find_function(mir, "run").unwrap()
expect_not(has_direct_call_named(run_fn, "inc"))
expect(count_indirect_calls(run_fn)).to_equal(0)
```

</details>

### fn reference constant LLVM emission

#### emits a struct-literal fn field as a function reference, not a string literal

- emits a struct-literal fn field as a function reference, not a string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a struct-literal fn field as a function reference, not a string literal")
val source = "struct Op:\n    f: fn(i64) -> i64\n\nfn double(v: i64) -> i64:\n    v * 2\n\nfn run() -> i64:\n    val op = Op(f: double)\n    (op.f)(4)\n"
val mir = lower_source(source)
val llvm = MirToLlvm.create("test.fn_param.struct_field", CodegenTarget.X86_64, nil).translate_module(mir)
assert_true(llvm.contains("ptr @double"))
expect_not(llvm.contains("c\"double\\00\""))
```

</details>

#### emits the indirect-call diamond as SSA-valid IR with a single merge load

- emits the indirect-call diamond as SSA-valid IR with a single merge load


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the indirect-call diamond as SSA-valid IR with a single merge load")
val mir = lower_source(apply_source)
val llvm = MirToLlvm.create("test.fn_param.apply", CodegenTarget.X86_64, nil).translate_module(mir)
assert_true(llvm.contains("call i64 @rt_closure_func_ptr"))
# the two arms store into one alloca slot and the join loads it
assert_true(llvm.contains("store i64"))
assert_true(llvm.contains("= load i64, ptr"))
expect_not(llvm.contains("undefined symbol"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fn-typed parameter call MIR lowering, fn reference constant LLVM emission.
- fn-typed parameter call MIR lowering
- fn reference constant LLVM emission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `1e92215c93445472fee5f4c224e7ad2f8925abf4343940254a59931c3511b4dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e92215c93445472fee5f4c224e7ad2f8925abf4343940254a59931c3511b4dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e92215c93445472fee5f4c224e7ad2f8925abf4343940254a59931c3511b4dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.spl
mirror: doc/06_spec/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a fn-typed parameter indirectly, never as a direct symbol call to its name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges the indirect-call result through one slot, not a multi-def temp' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir/fn_typed_parameter_indirect_call_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes a named function as the argument, keeping the outer call direct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
