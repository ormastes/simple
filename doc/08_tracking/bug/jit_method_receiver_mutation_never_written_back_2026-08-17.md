# Bug: a mutating method call on a `struct` receiver is silently discarded (JIT); an explicit `mut` struct parameter is silently discarded (interpreter)

- **Date:** 2026-08-17
- **Status:** OPEN — re-reproduced on the 2026-08-17 12:58 seed. **Both halves
  now root-caused to exact lines** (see the two "Root cause" sections at the
  bottom); both are Rust-seed changes, so no `.spl` fix is possible.
- **Severity:** P1, HIGH — silent wrong result. Compiles clean, exits 0, prints a
  plausible number that is simply wrong.
- **Found by:** the c_frontend triage lane, while attempting to reproduce
  `selfhost_two_hop_field_method_mutation_lost_2026-07-27.md`. That bug's
  interpreter half is fixed; this is what is left, and it is worse and differently
  shaped than what was filed.

## Symptom

```simple
struct Leaf:
    var n: i64

impl Leaf:
    fn bump():
        self.n = self.n + 1
        print("  inside bump, n now=" + self.n.to_text())

fn main():
    var l = Leaf(n: 0)
    l.bump()
    l.bump()
    print("depth0=" + l.n.to_text())
```

Executed 2026-08-17 on the deployed seed (`bin/simple`, mtime 2026-08-16 22:59),
rc=0 in both runs:

| engine | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=jit` (**the default for `bin/simple run`**) | `inside bump, n now=1` / `inside bump, n now=1` / **`depth0=0`** |
| `SIMPLE_EXECUTION_MODE=interpreter` | `inside bump, n now=1` / `inside bump, n now=2` / `depth0=2` |

The method **genuinely runs** and observes its own write — `self.n` reads back as
`1` inside the body — and then the mutated receiver is discarded at return. The
second call starts from `0` again. Nothing is printed to stderr and the exit code
is 0.

This is depth **zero**: the receiver is a plain local variable. It is the most
basic mutation shape in the language.

## The real axis is VALUE TYPES, not hop depth

`selfhost_two_hop_field_method_mutation_lost_2026-07-27` framed this as a
*hop-depth* defect (depth >= 2 loses the write) that affected the *interpreter*
while the JIT was correct. Measured today, every part of that framing is now
wrong. The class-detection probe
(`test/01_unit/compiler/codegen/probe_receiver_mutation_writeback_class_jit.spl`)
sweeps the axes; rc=0 on both arms:

| shape | interpreter | JIT |
|---|---|---|
| `struct` receiver, `self.n = self.n + 1` | ok (1) | **LOST (0)** |
| `class` receiver, same body | ok (1) | ok (1) |
| explicit `mut` struct **parameter** (`fn bump_param(mut c: SCounter)`) | **LOST (0)** | ok (1) |
| call delegated through another method (`self.bump()` inside `bump_twice()`) | ok (2) | ok (2) |
| struct receiver bumped 3x in a `while` loop | ok (3) | **LOST (0)** |
| depth-3 struct method call `deep.l2.l3.c.bump()` | ok (1) | **LOST (0)** |
| depth-3 direct field **assignment** `deep2.l2.l3.c.n = ... + 1` | ok (1) | ok (1) |

Four conclusions, all probe-proven:

1. **Depth is irrelevant.** Depth 0 fails on the JIT exactly like depth 3. The
   old bug's depth table was measuring the interpreter, which has since been
   fixed at all depths.
2. **The axis is value-type (`struct`) receivers.** `class` is reference-typed
   and is correct on both engines. This is why the defect survived: ECS/service
   code that happened to use classes never saw it.
3. **Neither engine is a safe control for the other.** They lose writes in
   *disjoint* places — the JIT loses `struct` receivers, the interpreter loses
   explicit `mut` struct *parameters*. Any A/B that assumes one engine is the
   oracle will draw the wrong conclusion, which is exactly what the 2026-07-27
   investigation did.
4. **The place model is fine; the write-back is missing.** The *direct
   assignment* spelling of the identical place (`deep2.l2.l3.c.n = ...`) is
   correct on both engines at depth 3. Only the *method-call* spelling loses the
   write. Loud-vs-silent asymmetry on the same operation is the whole reason this
   is hard to notice.

## Relationship to the already-fixed interpreter bug

The interpreter half of `selfhost_two_hop_field_method_mutation_lost_2026-07-27`
is **fixed in-tree**, classified by CONTENT (not by SHA, per the triage rule):

- `src/compiler_rust/compiler/src/interpreter/place.rs` now exists as a general
  place model; its header references the old
  `"deeply nested field access requires intermediate variables"` error it
  replaced.
- `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:23` documents
  repairing exactly the method-receiver path that used to be "silently evaluated
  as a value copy".
- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:975`
  `merge_shared_collection_fields` propagates Array/Dict/ByteArray fields from
  callee to caller.

That third function is the likely home of the **interpreter's** residual
`mut`-parameter gap: it deliberately keeps scalars and nested structs
value-typed, which is right for a plain by-value parameter and wrong for one the
author explicitly annotated `mut`.

The **JIT** half is not root-caused here. It lives in the lowering of a mutating
method's receiver (`20.hir/hir_lowering/**`, `50.mir/**`, `70.backend/**`), all of
which are owned by other live sessions as of 2026-08-17 — this lane deliberately
did not edit them.

## Blast radius

Any `struct` with an `impl` method that mutates `self`, executed through
`bin/simple run` / any compiled path. The write is lost with no diagnostic. Note
that `bin/simple test` hard-defaults to the interpreter, so **the entire spec
suite is blind to the JIT half** — a spec asserting the correct value passes
while the shipped engine returns the wrong one.

## Regression coverage added

- `test/01_unit/compiler/codegen/probe_struct_receiver_mutation_persist_jit.spl`
  — run-path probe, absolute-literal oracles, one verdict line.
- `test/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.spl`
  — reproducing spec; subprocesses the probe under both engines.
- `test/01_unit/compiler/codegen/probe_receiver_mutation_writeback_class_jit.spl`
  — class probe, the axis sweep tabulated above.
- `test/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.spl`
  — class-detection spec.

Both specs assert the CORRECT answer on both arms and are therefore **expected to
be RED** until the two write-back gaps are closed. Per `.claude/rules/testing.md`
a correct spec that fails is a legitimate artifact — do not soften them.

### Executed verdicts (RED, 2026-08-17)

`bin/simple test` never reached a verdict on either spec (one run: 1942 lines,
rc=0, **no `Results:` line** — the live
`test_runner_emits_no_result_summary_silent_exit0_2026-08-17` silent green; the
other: `Terminated`, **rc=143**, also no `Results:` line). Both verdicts below
come from `bin/simple run <spec>`, which bypasses the test daemon:

```
2 examples, 1 failure
SPEC FILE VERDICT: test/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.spl declared>=2 executed=2 passed=1 failed=1 dropped=0

2 examples, 2 failures
SPEC FILE VERDICT: test/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.spl declared>=2 executed=2 passed=0 failed=2 dropped=0
```

The reproducing spec's split is the designed shape: the interpreter control arm
**passes**, the JIT arm **fails**. The class spec fails on **both** arms, and the
two arms report **different** failure sets —

- interpreter arm: `FAIL mut_parameter expected 1 got 0` (everything else PASS)
- JIT arm: `FAIL struct_receiver`, `FAIL loop_three_calls`, `FAIL depth3_method`
  (with `mut_parameter` PASSing)

— which is also the **non-vacuity proof for engine selection**. A spec subprocess
can silently fail to honour `SIMPLE_EXECUTION_MODE` and run the interpreter under
a "jit" label (observed by another lane the same day); here the two arms produce
disjoint results, so they demonstrably reached different engines.

The class probe deliberately **excludes** Array/Dict/ByteArray receivers: one
unsupported container operation silently demotes the whole program to the
interpreter, which would make the JIT arm measure the wrong engine and report a
false green. Containers need a separate probe file.

## Reproduction

```sh
P=test/01_unit/compiler/codegen/probe_struct_receiver_mutation_persist_jit.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple run $P    # RECEIVER_MUTATION PROBE: ALL PASS
SIMPLE_EXECUTION_MODE=jit         bin/simple run $P    # RECEIVER_MUTATION PROBE: 4 FAILURES
```

Both exit 0. That is the defect.

---

## Re-verification 2026-08-17 (rebuilt seed) — STILL OPEN, both halves

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
**59,537,240 bytes, mtime 2026-08-17 12:58:51** (the table above was measured on
the 2026-08-16 22:59 seed).

Minimal repro from the Symptom section, verbatim:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run p1.spl ; rc=$?
depth0=2      rc=0
$ SIMPLE_EXECUTION_MODE=jit         bin/simple run p1.spl ; rc=$?
depth0=0      rc=0
```

Axis sweep re-run (`p1b.spl`: `mut` struct param, class receiver, struct
receiver bumped 3x in a `while`), one program, both engines, rc=0 on both:

| shape | interpreter | JIT | expected |
|---|---|---|---|
| `fn bump_param(mut c: SCounter)` | **0 (LOST)** | 1 | 1 |
| `class CLeaf` receiver | 1 | 1 | 1 |
| `struct Leaf` receiver, 3 calls in a loop | 3 | **0 (LOST)** | 3 |

Unchanged from the filed table: the two engines still lose writes in **disjoint**
places, and neither is a safe oracle for the other.

## Root cause — interpreter half (`mut` struct parameter), PINNED

`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:1185`

```rust
if !is_value_type_struct(callee_val, classes)
    && matches!(callee_val, Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_))
    && outer_env.contains_key(&caller_name)
{ ... full write-back ... }
else if is_value_type_struct(callee_val, classes) {
    // only merge_shared_collection_fields — containers only
}
```

`param_is_mut` is computed at `:1172-1176` and is used at `:1179` (alias
protection) and `:1193` (bookkeeping) — but **never in the branch condition at
`:1185`**. So a `struct` argument is routed by TYPE alone: because
`is_value_type_struct` is true, it always falls to the `else if` at `:1197`,
which only propagates `Array`/`Dict`/`ByteArray` fields. A scalar field write
(`c.n = c.n + 1`) has no container to ride back on and is dropped, *even though
the author explicitly wrote `mut c: SCounter`*.

The value-semantics rule the `else if` implements is correct for a **plain**
by-value parameter (`function_exec.rs:1009-1015` states that intent) and wrong
for an explicitly `mut`-annotated one — `mut` is precisely the opt-out. Fix
shape: make `:1185` take the full write-back branch when `param_is_mut` is true,
regardless of `is_value_type_struct`, leaving non-`mut` parameters on today's
container-only merge. Rust seed change — needs a rebuilt seed, so this lane
localized rather than patched.

## Root cause — JIT half (struct receiver), PINNED

The record above left this "not root-caused". It is now pinned, and it is **not**
in Cranelift: the receiver is copied by the *callee*, in MIR lowering.

`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1950-1953` — every
non-mutable parameter of a function, **including the implicit `self` of a
`fn`-declared method**, is deep-copied into its own slot at function entry:

```rust
for (i, param) in func.params.iter().enumerate() {
    if !param.is_mutable() {
        self.copy_param_if_value_type(i, param.ty)?;
    }
}
```

The surrounding comment (`:1946-1949`) states the intent: the copy must land
before the body is lowered so *"every read of an ordinary by-value parameter
inside the body must see the copy, not the caller's original"*. `fn bump()` is
declared `fn`, not `me`, so its implicit `self` is non-mutable and is copied. The
body then mutates the copy — which is exactly why `self.n` reads back `1` inside
the body while the caller's `l.n` stays `0`.

- `lowering_core.rs:1018` — `copy_param_if_value_type` ("site J") loads the
  param and stores an `AggregateCopy` back into the slot.
- `lowering_core.rs:929` — the gate that makes this **struct-only**:
  `if self.type_value_kinds.get(&name) != Some(&true) { return Ok(src); }`.
  A `class` has `Some(false)`, so it is never copied and the caller's handle is
  preserved. **That single line is why the axis is value-types, exactly as the
  probe table said.**

There is no compensating write-back at the call site, so nothing repairs it:

- `mir/lower/lowering_expr_method.rs:1323` — `let mut receiver_reg = self.lower_expr(receiver)?;`
- `lowering_expr_method.rs:2035-2040` and `:2058-2063` — the receiver is handed
  to `MirInst::MethodCallStatic { receiver: receiver_reg, .. }` as a plain value.
  The trailing comments at `:2043-2049` / `:2066-2072` say explicitly *"Do NOT
  store the push result back to the receiver variable"* — i.e. **no write-back
  mechanism exists on this path at all**. Virtual twin at `:2018-2024`.
- Cranelift merely honours that: `codegen/instr/closures_structs.rs:915-919`
  prepends the receiver as argument 0 by value, and `:924-933` binds only
  `results[0]` to `dest`, storing nothing back into the receiver's local slot
  (cross-module twin at `:1083-1097`).

### Why "direct assignment at depth 3 works but the method call doesn't"

Conclusion 4 of the probe table is explained by this: `deep2.l2.l3.c.n = ...` is
lowered as a place write in the *caller's own frame*, which never crosses the
entry-copy at `:1951`. Only the method-call spelling enters a callee and hits the
copy.

### Fix locus (two options, both Rust seed)

1. `lowering_core.rs:1951` — exclude the implicit `self` parameter of a struct
   `impl` from the entry copy, so the method mutates the caller's aggregate.
   Narrowest change, but must not weaken value semantics for a struct passed as
   an ordinary argument.
2. `lowering_expr_method.rs:2035` / `:2058` — emit a store-back of the mutated
   receiver into the receiver local after `MethodCallStatic`, when the receiver
   is a struct local. Requires the callee to expose the mutated aggregate.

Note the two halves of this record want **opposite** movements — the interpreter
half needs *more* write-back (honour `mut`), the JIT half needs *less* copying
(honour a mutating receiver). Fixing one does not fix the other, and neither
engine may be used as the oracle for the other's fix.
