# Native path: bool-returning string methods print as "1"/"0"; `.to_string()` on primitives unresolved outside SIMPLE_BOOTSTRAP=1 (and type-unaware even when gated on)

**Date:** 2026-07-17
**Severity:** Medium-High (silent wrong output for the first half; loud build
error for the second — bundled here because they share one root cause: lost
type information for bool/float results)
**Status:** source-fixed with focused MIR regressions; native execution pending
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Part A — `starts_with`/`ends_with`/`contains` interpolate as integers, not booleans

```simple
fn main():
    val a = "hello"
    print "O9:{a.starts_with(\"he\")}|END"
    print "O10:{a.ends_with(\"lo\")}|END"
    print "O11:{a.contains(\"ell\")}|END"
```

- Oracle: `O9:true|ENDO10:true|ENDO11:true|END`
- Native: `O9:1|ENDO10:1|ENDO11:1|END`

### Root cause

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` registered
the dedicated `starts_with` and `ends_with` runtime-call results as
`MirType.i64()`. The shared text-method fallback also sent `contains` through
the default i64 destination arm:

```
val ts_dest_ty = match method:
    case "replace" | "trim" | "lower" | "to_lower":
        MirType(kind: MirTypeKind.Opaque("str"))
    case _: MirType.i64()
```

All three therefore lost their logical boolean type. Downstream,
string-interpolation coercion
(`expr_dispatch.spl` ~line 274) picks the render function by inspecting the
local's registered MIR type
(`is_bool`/`is_float`/`is_u64` → `rt_raw_bool_to_string` /
`rt_raw_f64_to_string` / else `rt_raw_i64_to_string`). Since the dest type says
i64, it renders through `rt_raw_i64_to_string`, printing `1`/`0` instead of
`true`/`false`.

### Part A resolution (2026-07-19)

The shared MIR lowering now records `starts_with`, `ends_with`, and `contains`
runtime-call results as `MirType.bool()` at their existing call sites. This
matches the LLVM runtime declarations and keeps boolean provenance for print
and interpolation. `text_bool_result_type_source_spec.spl` pins all three
paths. The focused pure-Simple test runner currently crashes before reporting
the scenario, so end-to-end native execution remains pending.

## Part B — `.to_string()` on `i64`/`f64`/`bool` is unresolved outside `SIMPLE_BOOTSTRAP=1`

```simple
fn main():
    val t = true
    print "T3:{t.to_string()}|END"
    val i = 7
    print "T4:{i.to_string()}|END"
```

Native build (with `SIMPLE_BOOTSTRAP` unset, as the task's own native-build
invocation convention specifies):

```
[mir-lower] WARNING: unresolved method call 'to_string' lowered to const-0 placeholder (silent-null risk, Task #145)
[ERROR] MIR error: MIR lowering error: unresolved method call: to_string
error: MIR lowering error: unresolved method call: to_string
```

This is a **loud** build failure (good — not silently wrong), but it means
`n.to_string()` cannot be used at all in a normal (non-bootstrap) native
build.

### Root cause

`method_calls_literals.spl` line 1316:

```
if method == "to_string" and args.len() == 0 and (rt_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1":
```

Every sibling handler in this same file for the identical "HIR type inference
never populated `receiver.type_`" situation (Bug #138, documented at line
888-895 in this same file: *"resolution == Unresolved ... is the actual
condition the untyped string-method fallbacks below need, on EITHER the
bootstrap flat-HIR path or the normal native-build path — both produce
Unresolved here for the same reason"*) gates on `resolution_is_unresolved`
instead — e.g. `starts_with` at line 1439:
`if method == "starts_with" and args.len() == 1 and resolution_is_unresolved:`.
The `to_string` handler (Task #144) is the one outlier still gated on the
`SIMPLE_BOOTSTRAP` env var rather than `resolution_is_unresolved`, which is
why it only works during bootstrap and hard-fails in ordinary native builds.

**Do not simply flip the gate to `resolution_is_unresolved` as a standalone
one-line fix** — see Part C.

## Part C — even gated correctly, the `to_string` handler renders every type as `i64`

The handler body (line 1327-1332) unconditionally calls
`rt_raw_i64_to_string` on the receiver, with no `is_bool`/`is_float` branch
(unlike the interpolation-coercion path in `expr_dispatch.spl`, which already
has this logic at ~line 274:
`val render_fn = if is_bool: "rt_raw_bool_to_string" elif is_float:
"rt_raw_f64_to_string" elif is_u64: "rt_raw_u64_to_string" else:
"rt_raw_i64_to_string"`).

If Part B's gate were widened to `resolution_is_unresolved` without also
fixing this, `true.to_string()` would silently produce `"1"` and
`3.5.to_string()` would silently produce a garbage string decoded from the
float's raw bit pattern as if it were an integer — trading a **loud** MIR
error for a **silent wrong answer**, which is strictly worse and exactly what
this lane's mandate says never to do.

### Parts B/C resolution (2026-07-19)

Primitive `to_string()` and `to_text()` recovery now runs inside the
`MethodResolution.Unresolved` arm only after custom struct-method recovery.
It accepts only known text or supported bool/numeric MIR types, reuses the existing
`coerce_concat_operand` bool/f32/f64/u64/integer renderer selection, and
normalizes the result through `rt_interp_cstr`. Unknown, boxed, aggregate, and
custom receivers retain the loud unresolved path. The focused MIR regression
has no `SIMPLE_BOOTSTRAP` dependency and requires each bool/f64/u64/i64
renderer once per conversion alias. Cranelift routes the f64 renderer through
an explicit f64-to-i64 runtime import instead of its generic all-i64 fallback.
Native execution remains pending because the
available pure-Simple test artifacts either crash before scenario output or
lack the `test` command.

## Expected

- Bool-returning string methods (`starts_with`, `ends_with`, `contains`, and
  any others sharing this dispatch arm) must register a `Bool` MIR dest type,
  not `i64`, so downstream interpolation/print/`to_string` all render
  `true`/`false`.
- `.to_string()` must work identically whether or not `SIMPLE_BOOTSTRAP` is
  set (gate on `resolution_is_unresolved` like its siblings), **and** must
  select the correct raw-render function based on the receiver's actual type
  (bool/float/u64/i64/str), reusing the same `is_bool`/`is_float`/`is_u64`
  detection already implemented in `expr_dispatch.spl`.

## Suggested direction

1. In `method_calls_literals.spl` ~line 1793, split the `case _:` arm so
   `starts_with`/`ends_with`/`contains`/`rfind`/`find` get an explicit `Bool`
   (or keep `find`/`rfind` as `i64` — they return indices, not booleans; only
   `starts_with`/`ends_with`/`contains` are boolean) MIR type as appropriate
   per method.
2. Recover primitive conversions only after custom method dispatch, then reuse
   `expr_dispatch.spl`'s existing bool/float/u64/integer render selection.
3. Re-run this lane's probes plus the full smoke matrix
   (`sh scripts/check/native-smoke-matrix.shs`) after the change, since this
   touches shared MIR codegen used by every method call in this dispatch
   table.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).
