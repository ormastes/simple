# `E-HIR-BLOCK-VALUE-TYPE-DECAYED` / `cannot convert object to int` blocks native-build of `io_runtime`

**Status:** RESOLVED 2026-08-24 — see "Root cause (measured)" below. The
filed signature was TWO defects, not one, and the headline one was a FALSE
diagnostic.
**Observed:** 2026-08-24
**Area:** 30.hir / 35.semantics (block tail expression type capture)

## Position in the chain

`use std.nogc_sync_mut.io_runtime` has now shed three blockers:

1. seed-interpreter expression-position `if val` binding gap — FIXED `9e3eb1adccd`
2. Return borrow-check false positive on `Ref`-containing functions — FIXED `9e3eb1adccd`
3. `E-BACKEND-LLVM-INST-ResultMatchSemantic` — FIXED in `838f5e2e08c` (see
   `llvm_backend_no_result_match_semantic_2026-08-24.md`); that signature is
   now measured at **0 occurrences**, down from 7.

This is what is underneath. It is a **distinct** defect, not a recurrence.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`,
`BUILD_RC=0`). Exit code read DIRECTLY into a variable on the line after the
command, never through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 1200 "$SEED" native-build control.spl -o control.bin > fix.log 2>&1
$ NB_RC=$?
NB_RC=1
$ grep -c ResultMatchSemantic fix.log
0
```

## Verbatim error

```text
error: semantic: type mismatch: cannot convert object to int
E-HIR-BLOCK-VALUE-TYPE-DECAYED: block tail expression type_ word became a
non-well-formed heap reference between capture and HirBlock construction;
substituting a placeholder
error: native-build worker exited with code 1.
```

The `E-HIR-BLOCK-VALUE-TYPE-DECAYED` line repeats many times; the
`cannot convert object to int` errors appear to be the downstream consequence
of the substituted placeholder type.

## Why this looks like the 2026-08-24 defect family

Same family as `7d657439fa8`, `c3c4357063e`, `eaac3400b86`, `51a7b28e220`: a
type word crossing a boundary and being **lost or replaced**, with the
consequence surfacing far from the cause. The diagnostic text is unusually
specific and self-aware — it says the type word "became a non-well-formed heap
reference **between capture and HirBlock construction**", i.e. the producer
already knows the value decayed in transit and chooses to substitute a
placeholder rather than fail. That substitution is what turns a type-word
lifetime bug into a misleading `object to int` mismatch downstream.

Suggested first measurement: find the emitter of
`E-HIR-BLOCK-VALUE-TYPE-DECAYED` and log the *pre-decay* type word plus the
span, so the failing block tail can be localized. The placeholder substitution
should probably be a hard error under a debug env flag, the same way
`SIMPLE_DEBUG_UNDEFINED_VAR=1` made the previous blocker localizable.

## Not this defect

Two further independent MIR-lowering gaps, measured on the same pass:

- `std.common.text` — `MIR lowering error: unresolved method call: index_of`
- `std.nogc_sync_mut.fs` — `MIR lowering error: undefined variable Dir`


---

## Root cause (measured) — 2026-08-24

Re-measured on a freshly built seed (`cargo build --release --bin simple`,
`BRC=0`), per the standing warning. The filed report conflated **two
independent defects**. Exit codes below were read DIRECTLY into a variable on
the line after each command, never through a pipe.

### Defect 1 — `E-HIR-BLOCK-VALUE-TYPE-DECAYED` is a TAUTOLOGY (false diagnostic)

`src/compiler/20.hir/hir_lowering/_Expressions/block_and_asm_lowering.spl`
PROBE A **unconditionally** re-forms every value-block tail as
`HirExpr(kind: …, has_type_: false, type_: nil, span: …)` — the containment
added for the arm64 stage4 SIGSEGV. PROBE B then tested
`hir_heap_ref_wellformed(block_value_expr.type_)`. `nil` is not heap-tagged, so
`rt_heap_ref_wellformed(nil)` is **0 by construction**
(`src/compiler_rust/runtime/src/value/objects.rs:395`,
`src/runtime/runtime_native.c:8418`). PROBE B therefore fired on **every**
value-position block, unconditionally.

It also contradicts `HirExpr`'s own contract, under which `has_type_` is the
authoritative presence bit and `type_` is meaningless when it is false.

A level-gated capture probe (`SIMPLE_DEBUG_HIR_BLOCK_TAIL=1`) settled it:

```text
    349 P-HIR-BLOCK-TAIL-CAPTURE: has_type_=false type_ok=false span_ok=true
```

**349 captures, 349 DECAYED firings, 0 `E-HIR-BLOCK-VALUE-TYPE-MALFORMED`,
0 `E-HIR-BLOCK-VALUE-SPAN-MALFORMED`.** Nothing ever decayed. The type was
never present at capture in the first place, and PROBE A destroyed nothing.
The message text ("became a non-well-formed heap reference between capture and
HirBlock construction") was flatly wrong — a stale assertion of exactly the
family the chain has been fixing all day.

The harm was real even though the diagnostic was not: the 349 bogus lines
pushed **95605 of 107605 bytes** of worker stderr into the middle-drop
truncator, hiding the genuine diagnostics underneath. After the fix, DECAYED
count is **0** and worker stderr fell to **28305 bytes**.

Fix: PROBE B now tests the span (the word the function actually carries
forward) and tests `type_` only when `has_type_` claims one is present.

### Defect 2 — the REAL blocker: raw `LoadGlobal` payload decode

With the noise gone, `cannot convert object to int` was still there — **3
occurrences, not 349**, i.e. never the same defect. It carried no callee and no
span, which is why it was unlocalizable.

`SIMPLE_DEBUG_AS_INT_BT=1` (a pre-existing hook in `value_impl.rs`) gave the
frame:

```text
simple_compiler::value::Value::as_int
simple_compiler::interpreter::expr::ops::eval_op_expr
simple_compiler::interpreter::expr::evaluate_expr
simple_compiler::interpreter::interpreter_extern::call_extern_function
```

— an extern *argument* failing to evaluate. A new level-gated attribution probe
(`SIMPLE_DEBUG_EXTERN_ARG=1`, in `interpreter_extern/mod.rs`) named it exactly:

```text
[DEBUG extern-arg] extern=rt_value_as_int arg_index=0 \
  arg_expr=Binary { op: ShiftRight, left: Identifier("load_symbol_slot"), right: Integer(32) } \
  err=semantic: type mismatch: cannot convert object to int
```

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` decoded the
`MirInstKind.LoadGlobal` payload RAW — `rt_enum_payload` + `rt_tuple_get` +
`slot >> 32` — on the commented premise that

> SymbolId is a one-field struct and can decay to its raw i64 when crossing the
> staged enum-payload ABI.

**Measured false on the seed's tree-walk interpreter**, which is the engine the
`native-build` worker runs: tuple slot 1 is a live `SymbolId` **Object**, the
`: i64` annotation does not coerce it, and `>> 32` reached `Value::as_int` and
failed the whole build.

Fix (minimal, semantics-preserving): read both slots through typed `MirInst`
accessors, the shape the `StoreGlobal` sibling in the same file
(`translate_store_global_at` → `inst.bootstrap_store_global_symbol_id()`) has
always used and which works on the same lanes. New twins in
`src/compiler/50.mir/mir_instruction_graph.spl`:
`bootstrap_load_global_dest_local_id()` / `bootstrap_load_global_symbol_id()`.
A typed match reads the id under BOTH representations, so the `>> 32` is
removed (with a typed match it would return garbage).

**Honest caveat carried forward:** the deleted comment also claimed that typed
re-wrapping "dereferences the scalar as an object in Phase 2 native compilers".
That claim was falsified only on the interpreter; Phase-2 behaviour rests on
the `StoreGlobal` precedent (same shape, same file, same lanes), not on a fresh
measurement — the tracked stage binaries are separately advisory-RED, so it
could not be measured today. The claim is recorded here rather than silently
deleted.

Also updated: the now-stale comment at `src/runtime/runtime_native.c` (~:3277)
which named `rt_value_as_int(load_symbol_slot >> 32)` as a load-bearing
raw-shift call site. That call site no longer exists; `rt_value_as_int`'s own
contract is unchanged, and P4 of
`src/runtime/test/rt_value_as_int_text_decode_selfcheck.c` pins the function's
behaviour, not the call site.

## Gate

`scripts/check/check-hir-block-tail-and-loadglobal-decode.shs` — `--selftest`
FIRST and FATAL (6 fixtures), verdict LAST. It does not grep source; it runs a
real `native-build` of an `io_runtime` importer and classifies the worker
output, reading the exit status directly into a variable on the line after the
command. Fixtures cover both must-PASS and must-FAIL directions, and F4 pins
that a non-zero exit with neither fenced signature is still a **FAIL**, so a
further blocker underneath can never launder into a green verdict.

The DEFAULT assertion is signature-absence, not exit 0, per the honest-gate
precedent — blocker #5 (below) means exit 0 is not yet achievable, and a gate
red at birth would pin nothing. `--require-success` asserts exit 0; flip it on
as the default once #5 lands.

Mutation-tested both directions, and the real end-to-end scan executed in both
modes (verbatim):

```text
MUTANT_ALWAYS_OK_RC=1
FAIL - selftest failed (8 fixture(s) run); the classifier is untrustworthy, no scan was performed
MUTANT_ALWAYS_FAIL_RC=1
FAIL - selftest failed (8 fixture(s) run); the classifier is untrustworthy, no scan was performed

$ BUILD_TIMEOUT=300 sh scripts/check/check-hir-block-tail-and-loadglobal-decode.shs
$ GATE_RC=$?
GATE_RC=0
selftest: 8 fixture(s) passed
PASS - 2 case(s) checked, 0 E-HIR-BLOCK-VALUE-TYPE-DECAYED and 0 object-to-int; native-build exited 124, NOT success -- blocker #5 is open (...); pass --require-success to assert exit 0

$ BUILD_TIMEOUT=300 sh scripts/check/check-hir-block-tail-and-loadglobal-decode.shs --require-success
FAIL - 2 case(s) checked, both fenced signatures are absent but native-build exited 124 and --require-success was given
GATE_STRICT_RC=1
```

## Retained probes (level-gated, default off)

Per `.claude/rules/code-style.md` (logs are not unused code):

- `SIMPLE_DEBUG_HIR_BLOCK_TAIL=1` — prints `has_type_` / `type_ok` / `span_ok`
  at block-tail CAPTURE, so any future DECAYED report can be attributed to a
  real decay rather than to this function's own placeholder substitution.
- `SIMPLE_DEBUG_EXTERN_ARG=1` — names the callee, argument index and argument
  expression when an extern argument fails to evaluate. This is the probe that
  turned an unlocalizable `cannot convert object to int` into a one-line
  answer; it is generic and will localize the whole class.


## Proof status (honest) — 2026-08-24

Both fenced signatures are gone, and the LoadGlobal accessor change is verified
not to break native codegen:

```text
$ timeout 3600 "$SEED" native-build control.spl -o control.bin
$ NB_RC=$?
NB_RC=124
$ grep -c "E-HIR-BLOCK-VALUE-TYPE-DECAYED" fix2.log
0
$ grep -c "cannot convert object to int" fix2.log
0

$ timeout 540 "$SEED" native-build hello.spl -o hello.bin
$ HRC=$?
HELLO_NB_RC=0
$ ./hello.bin
hello
$ RUN_RC=0
```

`NB_RC=0` for the `io_runtime` importer is **NOT** claimed and is not yet
achievable: a FIFTH blocker sits underneath — `native_compile` does not
terminate. Filed as
`doc/08_tracking/bug/native_compile_nonterminating_io_runtime_2026-08-24.md`.
The gate is deliberately left asserting the real end state (exit 0), so it
reports that hang as a FAIL rather than being softened to a signature-only
green.

**Landed:** `be3e6fe4a21`


## Defect-class neighbour, checked and CLEARED

The sibling raw-looking decode in the same file —
`rt_value_as_int(packed_return_local & 0xFFFFFFFF)` in the `Ret` terminator arm
of `core_codegen.spl` — was inspected for the same premise and is **not** the
same defect. Its input comes from the typed accessor
`blocks[block_index].bootstrap_ret_local_id()`, i.e. already the shape this fix
moved LoadGlobal onto, not from `rt_enum_payload` / `rt_tuple_get`. It is
additionally guarded by `if packed_return_local > 0xFFFFFFFF`, an i64
comparison that a live object could not reach silently. No change made.
