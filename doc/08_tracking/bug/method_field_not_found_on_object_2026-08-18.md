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

## Resolution (2026-08-18, lane `lane-test-fix`)

**Fix applied: option (a) — `Value::aggregate` builds `Value::Object`
unconditionally** (`src/compiler_rust/compiler/src/value.rs`). The rest of
`981c88435e0` (struct zero-fill, the nested-call `ClassInstance` arm in
`interpreter_helpers/method_dispatch.rs`) is untouched; that arm simply becomes
dead for freshly constructed values.

**Why (a) and not (b):** grepped every non-vendor consumer of `ClassInstance` —
only six files (`interpreter/node_exec.rs`, `value_impl.rs`, `value_bridge.rs`,
`interpreter_helpers/method_dispatch.rs`,
`interpreter_call/core/class_instantiation.rs`, `value_pointers.rs`), and every
one of them handles `Value::Object` and `Value::ClassInstance` as parallel arms
rather than depending on reference-class identity. Nothing is load-bearing on
the split, so completing the port buys no behaviour today while requiring an
audit of hundreds of `Value::Object` pattern matches. Restoring correctness on a
severe `main` regression outweighs finishing the refactor in the same change.

**Follow-up (re-land, not dropped):** a `TODO(class-instance)` is recorded at the
`Value::aggregate` definition. Re-landing reference-class identity requires, in
one change: `Value::ClassInstance` arms in BOTH primary resolution paths
(field access `interpreter/expr/calls.rs:359`, method dispatch
`interpreter_method/mod.rs:1242`), routed through `aggregate_class()` /
`aggregate_field()`, plus an audit of the remaining `Value::Object` matches in
the interpreter.

**Regression guards shipped** (both reproduce on the unfixed seed, both green on
the fixed build):

- `test/01_unit/compiler/interpreter/class_instance_field_method_regression_spec.spl`
  — the minimal reproduction (class field read, class method call) with the
  byte-identical `struct` as positive control.
- `test/01_unit/compiler/interpreter/class_instance_resolution_class_spec.spl`
  — the defect class: static constructor, mutating `me` method, trait-`impl`
  block method, class held in a collection, cross-module class
  (`common.ui.ui_frame_clock.FixedStepClock`), plus struct and
  primitive/collection positive controls.

### Verification numbers (private seed build, `bin/simple` never touched)

Built with `CARGO_TARGET_DIR=/mnt/data/tmp/classfix`; GREEN runs used a symlink
shadow root (`/mnt/data/tmp/shadow`) so specs resolving `$REPO/bin/simple` picked
up the fixed binary without replacing the shared symlink.

| target | RED (shared seed) | GREEN (fixed) |
|---|---|---|
| `test/01_unit/hardware` | `Results: 386 total, 221 passed, 165 failed, 132 skipped` | `Results: 386 total, 268 passed, 118 failed, 85 skipped` |
| `test/01_unit/lib/common/ui/ui_frame_clock_spec.spl` | `Results: 5 total, 0 passed, 5 failed` | `Results: 5 total, 5 passed, 0 failed` |
| `test/shared/core/math_spec.spl` (positive control) | `Results: 34 total, 34 passed, 0 failed` | `Results: 34 total, 34 passed, 0 failed` |
| `class_instance_field_method_regression_spec.spl` | `Results: 4 total, 2 passed, 2 failed` | `Results: 4 total, 4 passed, 0 failed` |
| `class_instance_resolution_class_spec.spl` | `Results: 7 total, 2 passed, 5 failed` | `Results: 7 total, 7 passed, 0 failed` |

`test/01_unit/browser_engine` RED completed at `Results: 769 total, 249 passed,
520 failed, 519 skipped`. **The GREEN run is INCONCLUSIVE — no `Results:` line.**
Two independent attempts both hung: the runner completed a first pass, restarted
into a fresh `[setup] discover: begin`, and then sat with a static log for over
an hour at ~0 CPU (1h52m elapsed, 1m49s CPU, gaining ~1s per 30s of wall clock).
Directionally the partial output moved the right way — the first attempt's
per-file tally was 9 PASS / 10 FAIL files where RED was 7 PASS / 50 FAIL — but a
run with no `Results:` line is not a pass and is not reported as one.

**Follow-up (open):** determine why `test/01_unit/browser_engine` hangs on the
fixed binary. The most likely explanation is that specs which previously aborted
immediately on the `object` error now execute for real and one of them does not
terminate; that would be a pre-existing defect unmasked by this fix rather than
caused by it, but it has NOT been proven either way and must not be assumed.
