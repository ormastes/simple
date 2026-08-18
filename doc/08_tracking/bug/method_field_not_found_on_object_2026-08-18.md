# BUG: every `class` (reference-type) instance loses field and method resolution in the Rust-seed interpreter

- **Status:** OPEN — root cause identified, fix is in the Rust seed (cannot be deployed from this lane)
- **Severity:** CRITICAL — dominant failure class in the 2026-08-18 full sharded test run (~8000 failures)
- **Found:** 2026-08-18, lane `lane-test-fix`
- **Regression from:** `981c88435e0` "fix(interpreter): nested-call dispatch on class instances and struct zero-fill" (2026-08-16 23:11:33 +0000)

## Symptom signatures

```
semantic: method `now_micros` not found on type `object` (receiver value: HostFrameClock())
semantic: method `init` not found on type `object` (receiver value: SoftwareBackend(...))
semantic: method `get_namespace_id` not found on type `object` (receiver value: ...)
semantic: undefined field 'x': cannot access field on value of type 'object'
```

The receiver is a real, correctly constructed instance — the constructor name and
every field print correctly in the diagnostic — yet both field read and method
dispatch fail. `object` is not a degraded type: `Value::type_name()`
(`src/compiler_rust/compiler/src/value_impl.rs:638`) maps **both**
`Value::Object` and `Value::ClassInstance` to the string `"object"`, which is why
the message looks like type loss when it is actually a missing match arm.

## Minimal reproduction (11 lines, ~2s)

`.shs` is used only to force the interpreter — `should_force_interpreter_for_source`
/ `should_prefer_interpreter_for_source`, `src/compiler_rust/driver/src/exec_core.rs:1428`.
The identical `.spl` runs fine because it goes through the JIT; the defect is
interpreter-only, which is exactly why `bin/simple test` (interpreted) is red.

```
class C:
    var x: i64
    me now() -> i64:
        self.x
fn main():
    var c = C(x: 3)
    print(c.x)
    print(c.now())
```

```
$ bin/simple run /tmp/rp3/v2.shs
error: semantic: undefined field 'x': cannot access field on value of type 'object'
$ bin/simple run /tmp/rp3/v1.shs      # same file, calling c.now()
error: semantic: method `now` not found on type `object` (receiver value: C(x: 3))
```

Change the single keyword `class` -> `struct` and the same file prints `3` / `3`.

## Exact triggering condition

**Any construction of a non-value-type aggregate (`class`, i.e.
`ClassDef.is_value_type == false`) in the interpreter, followed by any field read
or method call on it.** It is unconditional: same-module or cross-module, plain
class or trait `impl`, class-body `me` method or `impl` block method, direct or
via a helper — all fail. `struct` (value type) is unaffected. The JIT/native path
is unaffected.

## Mechanism

`981c88435e0` introduced `Value::aggregate` (`src/compiler_rust/compiler/src/value.rs:1338`):

```rust
pub fn aggregate(class: String, fields: HashMap<String, Value>, is_value_type: bool) -> Self {
    if is_value_type {
        Value::Object { class, fields: Arc::new(fields) }
    } else {
        Value::ClassInstance(Arc::new(ClassInstance::new(class, fields)))
    }
}
```

and rewrote every construction site in
`src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`
(lines 179, 263, 278, 317, 461) from a literal `Value::Object { .. }` to
`Value::aggregate(..., class_def.is_value_type)`. Before that commit every
interpreted instance was a `Value::Object`; after it, every `class` instance is a
`Value::ClassInstance`.

The two primary resolution paths were never given a `ClassInstance` arm:

- Field access — `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:359`
  matches `Value::Object { ref fields, ref class, .. }` (direct `fields.get(field)`,
  then `get_`/`is_` auto-getters, then impl-block methods). A `ClassInstance`
  receiver falls through every arm to the `_` arm at line ~975 and produces
  `undefined field '{field}': cannot access field on value of type 'object'`
  (calls.rs:1002).
- Method dispatch — `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1242`
  matches `Value::Object { class, fields }` and calls `find_and_exec_method`.
  A `ClassInstance` receiver reaches the generic tail at mod.rs:1667 and produces
  ``method `{m}` not found on type `object` (receiver value: ...)``.

Verified by grep: `ClassInstance` occurs **0 times** in both
`interpreter_method/mod.rs` and `interpreter/expr/calls.rs`.

The commit's own code comment states the opposite premise and is factually wrong:

```
// Mutable class instances in chained/nested position ...
// The primary method evaluator handles Value::ClassInstance receivers, but this
// nested-call dispatcher previously had no arm for them ...
```
(`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:751-759`)

The nested-call dispatcher (`method_dispatch.rs:760`) got the new arm; the
*primary* evaluator it claims already handles `ClassInstance` does not. That
inverted assumption is the whole defect.

## Regression verdict

**NEW regression, introduced by `981c88435e0` (2026-08-16).** Evidence:

- `git show 981c88435e0 -- .../class_instantiation.rs` shows the construction
  sites changing from literal `Value::Object` to `Value::aggregate(..., is_value_type)`.
  Before the commit, no interpreted `class` instance could be a `ClassInstance`.
- `struct` vs `class` is the exact switch, matching `is_value_type` — the only
  discriminator `Value::aggregate` uses.

**Explicitly ruled out — the env-cache port is NOT the cause.** The suspected
`captured_env_with_live_globals` / `GenTrackedCell` cache (`7dc9d1f962f`) was
disabled via its kill switch and the failure is byte-identical:

```
$ SIMPLE_INTERP_ENV_CACHE=0 bin/simple test test/01_unit/lib/common/ui/ui_frame_clock_spec.spl --no-cover-check
    semantic: method `now_micros` not found on type `object` (receiver value: FixedStepClock(current_us: 0, step_us: 1000))
    ... Results: 5 total, 0 passed, 5 failed        # identical to the cached run
```

## Blast radius

Effectively **all** interpreted `class`-based code, which plausibly accounts for
the large majority of the ~8000 failures:

- `test/01_unit/lib/common/ui/ui_frame_clock_spec.spl`: 5 total, 0 passed, 5 failed.
- A spec whose class is declared **inside the spec file itself** fails the same
  way (`LocalClock(current_us: 0)`), so no import/module condition is needed.
- The **test runner's own** reporting code fails on the same defect after the
  results line: ``method `add_row` not found on type `object` (receiver value:
  SdnTable(index: {}, rows: [], columns: [id, value], name: strings))`` — i.e.
  the harness itself is damaged, not just the specs.

Only specs that stay entirely on `struct`s, primitives, or the JIT path escape.

## Proposed fix (Rust seed — cannot be deployed from this lane)

Preferred, smallest and safest: **make `Value::aggregate` construct
`Value::Object` unconditionally** (revert the `is_value_type` branch), keeping the
rest of `981c88435e0` — the struct zero-fill and the nested-call `ClassInstance`
arm are harmless and the latter simply becomes dead for freshly constructed
values. This restores pre-`981c88435e0` behaviour for every path in one line.

If `ClassInstance` is genuinely wanted for reference-class identity/mutation,
then it must be a complete port, not a partial one: add `Value::ClassInstance`
arms to **both** primary paths — the field-access match at
`interpreter/expr/calls.rs:359` and the method-dispatch match at
`interpreter_method/mod.rs:1242` — routing through the existing
`Value::aggregate_class()` / `aggregate_field()` helpers, plus an audit of every
remaining `Value::Object { .. }` pattern match in the interpreter (34 sites
mention `ClassInstance` today versus hundreds that match `Value::Object`).

Do NOT weaken or skip any spec: the specs are correct and the seed is wrong.

## Fix verified experimentally (private seed, `bin/simple` untouched)

A private seed was built at HEAD with `CARGO_TARGET_DIR=/mnt/data/tmp/obj-bisect`
(the shared `bin/simple` symlink was never modified). It reproduces:

```
=== HEAD build repro ===
error: semantic: method `now` not found on type `object` (receiver value: C(x: 3))
error: semantic: undefined field 'x': cannot access field on value of type 'object'
```

The same tree with `Value::aggregate` collapsed to a single `Value::Object`
construction (the proposed one-line fix), rebuilt into the same private target
dir, passes both:

```
=== PATCHED build ===
3
3
```

The patch was reverted from the worktree immediately after the measurement
(`src/compiler_rust/compiler/src/value.rs` is clean); the fix must be landed and
deployed by whoever owns the seed lane.
