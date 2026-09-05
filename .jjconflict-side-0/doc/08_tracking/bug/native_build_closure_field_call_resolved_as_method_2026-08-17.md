# Calling a closure-valued FIELD as `self.f(...)` is resolved as a METHOD call on the class

- **Filed:** 2026-08-17
- **Status:** RESOLVED 2026-08-17 (fixed in the seed interpreter by `cfe08d5732d`,
  "fix(interpreter): generalize callable-field method-call syntax"; re-verified
  below on the seed rebuilt 2026-08-17 12:58). The `parallel.spl` local-binding
  workaround and its two guard specs are kept — they are harmless and pin the
  shape.

## Re-verification 2026-08-17 (seed rebuilt 12:58)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59537240 bytes,
mtime 2026-08-17 12:58:51.

Case 1 — named fn in an `any` field, `self.cb(a, b)`:

```
$ bin/simple run <scratch>/closure.spl
RC=0
[INFO] JIT compilation failed, falling back to interpreter: ... deferring to interpreter
result=7
```

Case 2 — lambda in the field, called both as `self.cb(...)` inside a method and
as `h.cb(...)` from outside the class:

```
$ bin/simple run <scratch>/closure2.spl
RC=0
inner=7
outer=11
```

Both previously-RED forms now produce the correct values; the
``method `cb` not found on class `Holder` `` error is gone. Root-cause fix is the
callable-field fallback routed through `call_value_as_callable`, landed in
`src/compiler_rust/compiler/src/interpreter_method/mod.rs` by `cfe08d5732d`.
- **Reported symptom:** multi-module native build fails on BOTH backends with
  `method owner_collect_fn not found on class ParallelBuilder`
  at `src/compiler/80.driver/driver_build/parallel.spl:248`.

## Summary

A postfix call on a member access, `self.<field>(args)`, is resolved as a
**method call on the receiver's class**, never as an **indirect call through the
value held in the field**. When the field holds a callable (a named `fn` or a
lambda) and no method of that name exists on the class, resolution errors out
instead of invoking the field's value.

This is not specific to `ParallelBuilder` or to `owner_collect_fn`. It is a
defect class: any closure-valued field on any class, called directly.

## Reproduction (verified 2026-08-17)

`bin/simple` here is the **Rust seed** (`bin/release/x86_64-unknown-linux-gnu/simple`,
built 2026-08-16), which prints its own bootstrap-seed warning. All four cases
below were run as `nice -n 19 bin/simple run <file> --timeout 600`.

### RED — named fn in an `any` field, called as `self.cb(a, b)`

```
class Holder:
    name: str
    cb: any

impl Holder:
    me call_it(a: i64, b: i64) -> i64:
        return self.cb(a, b)

fn add_two(a: i64, b: i64) -> i64:
    return a + b

fn main():
    val h = Holder(name: "h", cb: add_two)
    val r = h.call_it(3, 4)
    print("result=" + r.to_string())
```

Verbatim output:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: function 'main' loads a named function as a callable value; the JIT closure ABI has no tag-boxed representation for a bare function pointer (compile_indirect_call would deref the raw code address as a closure struct and call garbage); deferring to interpreter
error: semantic: method `cb` not found on class `Holder`
```

### RED — lambda in an `any` field, called as `self.cb(a, b)`

Same class, `val add = |a: i64, b: i64| a + b` passed as `cb`:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: function 'main' creates a lambda/closure; the JIT closure ABI does not tag-box lambda arguments or results and is incompatible with the runtime's RuntimeClosure layout, so JIT would return wrong values or crash; deferring to interpreter
error: semantic: method `cb` not found on class `Holder`
```

So the defect is independent of whether the callable is a named function or a
lambda.

### GREEN — same lambda, bound to a local first

```
    me call_it(a: i64, b: i64) -> i64:
        val f = self.cb
        return f(a, b)
```

```
[INFO] JIT compilation failed, falling back to interpreter: ... deferring to interpreter
result=7
```

Binding the field value to a local and calling the local is the working
source-level form.

### Field access outside a method is affected identically

`h.cb(3, 4)` at a call site outside the class fails the same way; the receiver
being `self` is not part of the trigger.

## Root cause

`/mnt/data/worktrees/simple-main/src/compiler_rust/compiler/src/interpreter_method/mod.rs:1859`

```rust
bail_unknown_method!(method, class.as_str(), available_methods);
```

This is the terminal `bail` of the `Value::ClassInstance` receiver path in
`evaluate_method_call`. Before reaching it, the path tries, in order:

1. `classes[class].methods`
2. `impl_methods[class]`
3. `TRAIT_IMPLS` for the type
4. `try_method_missing`
5. `try_bare_some_option_method`
6. UFCS fallback — a free function whose name matches the method

and then errors. **There is no step that looks at the instance's FIELDS for a
callable value.**

The contrast that proves this is an oversight rather than a design choice is the
sibling `Value::Object { class, fields }` arm in the *same function*, whose
terminal bail is at `interpreter_method/mod.rs:1338`. That arm *does* consult
the fields first, at `interpreter_method/mod.rs:1297`:

```rust
if let Some(result) = crate::interpreter::interpreter_call::call_value_as_callable(
```

`call_value_as_callable` handles Lambda / Function / BlockClosure /
NativeFunction / Constructor / `__call__`. `Value::Object` receivers therefore
support closure-valued-field calls; `Value::ClassInstance` receivers do not.
A `class ... :` declaration produces a `ClassInstance`, which is why every class
in `src/compiler/**` hits the broken path.

The error text itself is produced by `bail_unknown_method!`, defined at
`/mnt/data/worktrees/simple-main/src/compiler_rust/compiler/src/interpreter/error_macros.rs:58-86`.

### Provenance caveat (important)

The literal string ``method `{}` not found on class `{}` `` does **not** appear
in `simple-main`'s own sources or git history — in this worktree the macro
renders the type-kind word differently. It *is* present in the rodata of the
deployed `bin/simple`, and verbatim in
`/mnt/data/worktrees/simple-v9-qualification-recovery/src/compiler_rust/compiler/src/interpreter_method/mod.rs:1243`.
**The `bin/simple` used for the reproduction above was built from a different
worktree than `simple-main`.** The structural defect (no callable-field fallback
on the `ClassInstance` arm) is present in `simple-main`'s own source at the
line cited above and was read directly there, so the root cause holds for this
tree; only the exact diagnostic wording is worktree-dependent.

## Fix

**Real fix (out of scope for the filing lane):** in the `Value::ClassInstance`
arm of `evaluate_method_call`, before `bail_unknown_method!` at
`interpreter_method/mod.rs:1859`, add the same callable-field fallback the
`Value::Object` arm already has at line 1297 — look up `method` in the
instance's fields and, if the value is callable, dispatch via
`call_value_as_callable`. This makes the two receiver representations agree.

The pure-Simple compiler (`src/compiler/**`) contains no such message and no
such dispatch path; this is purely a Rust-seed interpreter defect.

**Workaround applied in `src/compiler/80.driver/driver_build/parallel.spl`:**
bind `self.owner_collect_fn` to a local before calling it, at both call sites.

## Ownership / scope

The root cause is in `src/compiler_rust/compiler/src/interpreter_method/mod.rs`,
which the filing lane may not edit (lane scope was
`src/compiler/80.driver/**`, `test/**`, `doc/08_tracking/bug/**`; the
method-resolution layers `src/compiler/{10.frontend,20.hir,50.mir,70.backend}`
and the Rust seed were explicitly forbidden). The compiler fix is therefore
**filed, not applied**, and is owned by whoever owns the seed interpreter's
method-dispatch layer.

## Regression guards

- `test/01_unit/compiler/driver/parallel_owner_collect_closure_field_call_spec.spl`
  — the reproducing guard: `parallel.spl` must not contain
  `self.owner_collect_fn(`, and must invoke the hook through a local binding.
- `test/01_unit/compiler/driver/driver_closure_field_call_class_detection_spec.spl`
  — the defect-class guard: sweeps every `.spl` under `src/compiler/80.driver`
  for any `self.<field>(` where `<field>` is a declared `any`-typed field, and
  self-tests its own scanner against a synthetic positive so a vacuous pass is
  impossible.

## Verification status of the guards (honest account)

### Reproducing spec — GREEN after the fix

```
  ✓ never calls the closure-valued field directly as self.owner_collect_fn(...)
  ✓ still declares the owner_collect_fn field and its setter
  ✓ invokes the collect hook through a local binding
SPEC FILE VERDICT: test/01_unit/compiler/driver/parallel_owner_collect_closure_field_call_spec.spl declared>=3 executed=3 passed=3 failed=0 dropped=0
Results: 3 total, 3 passed, 0 failed
rc=0
```

The corresponding RED is established by CONTENT, not by a `Results:` line — the
pre-fix run timed out in the harness before the fix landed. The pre-fix source
is recoverable at `3135fde42df~1`, and contains exactly what the spec forbids:

```
$ git show 3135fde42df~1:src/compiler/80.driver/driver_build/parallel.spl | grep -n 'self.owner_collect_fn('
336:                            collect_error = self.owner_collect_fn(build_unit.path, output)
399:                                    collect_error = self.owner_collect_fn(build_unit.path, output)
```

Assertion 1 (`contains("self.owner_collect_fn(")` must be false) and assertion 3
(local binding must be present) both fail against that content, so the spec is
demonstrably not vacuous. The defect-class scanner over the same pre-fix blob
reports `OFFENDER owner_collect_fn`.

### Class-detection spec — GREEN

```
  ✓ finds no self.<any-typed field>(...) call sites anywhere under 80.driver
  ✓ detects the defect shape when it is present (self-test of the scanner)
SPEC FILE VERDICT: test/01_unit/compiler/driver/driver_closure_field_call_class_detection_spec.spl declared>=2 executed=2 passed=2 failed=0 dropped=0
Results: 2 total, 2 passed, 0 failed
rc=0
```

Its first RED was **a defect in the spec itself, not a detection of the bug** —
`shell()` returns a `ProcessResult`, so `.trim()` on it failed:

```
  ✗ finds no self.<any-typed field>(...) call sites anywhere under 80.driver
    semantic: method `trim` not found on type `ProcessResult`
Results: 2 total, 0 passed, 2 failed
```

Fixed by reading `.stdout` first. Two earlier attempts before that produced no
`Results:` line at all (one harness timeout, one `rc=143` SIGTERM) — both
**UNVERIFIED, not failed**.

Note the honest limitation: because the spec was only made runnable *after* the
source fix landed, it has **never been observed failing on the real defect**.
Its non-vacuity rests on the second example, which builds a synthetic file
containing the defective shape and asserts the scanner flags it. The
defect-detection RED itself is evidenced by running the scanner directly against
the pre-fix blob (`OFFENDER owner_collect_fn`), not by the harness.

A stale-daemon transcript from the earlier attempts, retained because it shows
how a non-verdict presents:

```
ERROR: test daemon timed out: test/01_unit/compiler/driver/parallel_owner_collect_closure_field_call_spec.spl
ERROR: no response from the light daemon within 900000ms + 2000ms grace.
SPEC FILE VERDICT: ... declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=daemon-no-response budget_ms=9000
```

`reason=daemon-no-response` — this is **UNVERIFIED, not failed**.

A second attempt at the class-detection spec was killed outright: the log
contains nothing but `rc=143` (SIGTERM), i.e. no `Results:` line and no spec
verdict at all. That too is **UNVERIFIED, not failed** — an rc of 143/144 with
no `Results:` line carries no information about whether the assertions hold. The light
daemon (`src/app/test_daemon/light_daemon.spl`, pid alive 39min, still writing
`responses/`) is not stale, merely saturated: the box carried ~57 processes
queued against `scripts/resource/test-slot.shs`'s 6 slots, and only **2 of 33**
`simple test` invocations in this session produced a verdict at all. Do not
`rm -rf .build/test_daemon_light` on this evidence — the lock is live and shared
with other sessions.

What *is* verified, by evaluating the specs' predicates directly rather than
through the harness:

- defect-class sweep before the fix: `OFFENDER src/compiler/80.driver/driver_build/parallel.spl:owner_collect_fn`
- after the fix: sweep clean, `self.owner_collect_fn(` occurrences `0`,
  local-bind occurrences `2`, local-call occurrences `2`

Both specs should be re-run for a real verdict once the host is quiet.

## Related

`src/lib/common/iterator/reduce.spl:24` already carries a comment recording the
same failure shape (``method `next_fn` not found on class `Iterator` ``), and
`src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl:239` records
another (``method `host_body_mutation_hook` not found on class JsInterpreter``).
Both are instances of this defect class that were previously worked around
in place without the root cause being filed.

---

## CORRECTION (2026-08-17, verification lane) — the Rust root cause above is WRONG; the live gap is in pure-Simple semantics

The section above places the root cause in
`src/compiler_rust/compiler/src/interpreter_method/mod.rs` ("no callable-field
fallback") and asks for one to be added at `:1859`. **That is not correct for
current source, and a fix there is inert.** Verified by building and ablating,
not by reading.

### The Rust seed interpreter is ALREADY FIXED in-tree

`interpreter_method/mod.rs:1244-1307` already implements the full callable-field
fallback on the instance-receiver path: `if let Some(field_value) =
fields.get(method)` handling `Value::Lambda`, `Value::Function`, and routing
`BlockClosure` / `NativeFunction` / `Constructor` / `Object` through
`interpreter_call::call_value_as_callable`.

The RED in this doc came from the **deployed `bin/simple`, which is a stale Rust
seed** (mtime `2026-08-16 22:59`). `strings bin/release/x86_64-unknown-linux-gnu/simple
| grep -c "not found on class"` = 1 — the backticked wording is baked into that
binary, and **no file under `src/**` emits it**. Current source does not produce
this diagnostic at all.

### Evidence — reproduce, fix, ABLATE

Probes (`Holder`/`C` class with a `cb: any` lambda field; `S` struct likewise):

| binary | `self.cb(x)` on class | `c.cb(x)` on class | `s.cb(x)` on struct |
|---|---|---|---|
| deployed stale seed `bin/simple` | `error: semantic: method \`cb\` not found on class \`Holder\`` | `error: ... on class \`C\`` | `B_struct=11` OK |
| built from current source, unmodified | `direct=42` OK | `A_extern=11` OK | `B_struct=11` OK |

Build: `CARGO_TARGET_DIR=/mnt/data/cargo-target-pm cargo build --release --bin simple`,
`Finished release profile in 10m 18s`. The struct-vs-class split visible in row 1
is what made this look like a class-path-only defect; it is really a
stale-binary artifact.

A candidate fix was written for the *other*, second `fields.get(method)` site in
the same file (`~:1785`, the `evaluate_method_call_with_self_update` mutable-self
path), whose match still ends in a bare `_ => {}` and therefore drops
`BlockClosure`/`NativeFunction`/`Constructor`/`Object`. It was **reverted** after
ablation: with the arm removed and everything else identical, all three probes
still pass (`direct=42`, `A_extern=11`, `B_struct=11`), so the probes never reach
that site and the change was unused code with no test to justify it. That
asymmetry is real but currently unreachable and unproven — noted here rather
than patched speculatively. `src/compiler_rust/**` is left pristine by this lane.

### The genuinely live gap (still OPEN): pure-Simple semantics has NO callable-field strategy

This is the one that actually breaks the **multi-module native build on both
backends**, because the native build runs the pure-Simple analyzer, not the seed
interpreter.

- `src/compiler/35.semantics/resolve_strategies.spl:32-55`, `resolve_method`.
  It tries exactly three strategies — `try_instance_method` (:36),
  `try_trait_method` (:41), `try_ufcs` (:47) — then errors at :53 with
  `"no method '{method}' found for type '{type_name}'"`. There is **no field
  lookup anywhere in the file**, so a callable-valued field is never a
  resolution candidate.
- `src/app/interpreter/expr/calls.spl:274-307`, `call_object_method`: on a
  `"{class}.{method}"` miss it tries only `to_string`/`clone` and then errors at
  :307, even though `fields` is in hand. Same missing fallback.

**Why this lane did not fix it:** the minimal fix needs a new
`MethodResolution.FieldCall(...)` variant, and `MethodResolution` is declared in
`src/compiler/20.hir/hir_types.spl` with the corresponding lowering in
`src/compiler/20.hir/hir_lowering/**` — both held by another lane. The
`80.driver` workaround (binding the field to a local before invoking) remains
required until that lands.

### Status

- Seed interpreter path: **ALREADY FIXED** in source; needs only a seed redeploy.
- Pure-Simple semantics path (`35.semantics` + `src/app/interpreter`): **OPEN**,
  root cause pinned to the file:line above.
