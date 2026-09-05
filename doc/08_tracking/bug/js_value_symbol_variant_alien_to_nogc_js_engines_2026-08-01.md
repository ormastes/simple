# `JsValue.Symbol` constructed and matched in engines whose `JsValue` has no `Symbol` variant

**Status:** FIXED — six alien `JsValue.Symbol` match arms removed.
**Severity:** high. Under the default JIT the *whole module* silently dropped to
the tree-walking interpreter ("expect ~100-1000x slowdown"); under
`SIMPLE_JIT_STRICT=1` and on the semantic path it is a hard error.

## Symptom

```
[jit-fallback] MIR lowering error: Unsupported HIR construct: unknown variant or
method 'Symbol' on enum JsValue: whole module dropped to the interpreter
(expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
error: semantic: unknown variant or method 'Symbol' on enum JsValue
```

Load-independent — not a timeout artifact.

## Three divergent `JsValue` enums

| Path | Variants | `JsProperty` | `JsObject` |
|---|---|---|---|
| `src/lib/common/js/types/js_types.spl` | 9 — incl. **`Symbol(id: i64)`** | key, value, writable, enumerable, configurable (+ `data`/`readonly` statics) | id, properties, prototype_id (+ statics) |
| `src/lib/js/types/js_types.spl` | 8 — **no `Symbol`** | key, value, enumerable | properties |
| `src/lib/nogc_sync_mut/js/types/js_types.spl` | 8 — **no `Symbol`** | key, value, enumerable | properties |

Only `common/` has `Symbol`. The other two are variant-identical to each other.

`src/lib/nogc_async_mut/js/` has **no** `types/js_types.spl` of its own and
imports the same tier-less path.

## Which enum the affected engines actually use — PROVED

The affected trees (`src/lib/nogc_sync_mut/js/`, `src/lib/nogc_async_mut/js/`,
`src/app/js/`) all import tier-lessly:

```
use std.js.types.js_types.JsValue
```

Three independent lines of evidence show this is *not* the `common/` enum:

1. **Constructor shape.** `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl:45`
   builds `JsProperty(key:, value:, enumerable:)` — three fields — and
   `JsObject(properties: props)` — one field. Neither is constructible against
   `common/`, which additionally requires `writable`/`configurable` and
   `id`/`prototype_id`. If these files resolved to `common/` they would fail on
   the constructors, not on `Symbol`.
2. **Tier self-identification.** Eight `export use std.nogc_sync_mut.…`
   re-exports in that tree (e.g.
   `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl` tail).
3. **Direct discriminator.** A probe containing only
   `use std.js.types.js_types.{JsValue}` plus `JsValue.Symbol(id: 1)` fails with
   the same `unknown variant` error — so the tier-less path resolves to a
   Symbol-less enum.

## Why `Symbol` is not part of these engines' contract

These engines model JS symbols as **text keys**, never as a `JsValue` variant:

- `src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl:154-159` returns
  `JsValue.String(v: "Symbol.iterator")`, `"Symbol.asyncIterator"`,
  `"Symbol.toPrimitive"`.
- `interpreter_native.spl` registers `"Symbol.iterator"` /
  `"Symbol.asyncIterator"` as ordinary string property names.
- `interpreter_object.spl:335` exposes the `Symbol` global as a native id.

So adding a `Symbol` variant to the Symbol-less enums would contradict the
engines' own representation and would have made the three-way divergence
permanent. The arms were the defect, not the enum.

## Sites fixed (the full family — 6, not 1)

| File | Line | Arm removed |
|---|---|---|
| `src/lib/nogc_sync_mut/js/engine/interpreter.spl` | 126 | `JsValue.Symbol(id): return JsValue.Symbol(id: id)` |
| `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl` | 654 | `JsValue.Symbol(id): return "null"` |
| `src/lib/nogc_sync_mut/js/conformance/runner.spl` | 91 | `JsValue.Symbol(id): "Symbol()"` |
| `src/lib/nogc_async_mut/js/engine/interpreter_async.spl` | 489 | `JsValue.Symbol(id): return "null"` |
| `src/lib/nogc_async_mut/js/conformance/runner.spl` | 91 | `JsValue.Symbol(id): "Symbol()"` |
| `src/app/js/main.spl` | 134 | `JsValue.Symbol(id): "Symbol()"` |

Each removal is behaviour-preserving: the arms were unreachable (the type has no
such variant, so no value could ever carry it). Every affected `match` still
covers all 8 real variants, and the three `_json_stringify` / `_simple_fetch_value`
sites additionally have explicit `"undefined"` / `JsValue.Undefined` fallthroughs.

## Evidence (RED before GREEN)

Probe harness compiles each module with a bare positional `.spl` (JIT lane) and
carries a known-good control fixture in the same run.

```
=== PRE-FIX ===                                === POST-FIX ===
CONTROL: CLEAN                                 CONTROL: CLEAN
nogc_sync_mut.js.engine.interpreter: SYMBOL_ERROR        -> CLEAN
nogc_sync_mut.js.engine.interpreter_async: SYMBOL_ERROR  -> CLEAN
nogc_sync_mut.js.conformance.runner: SYMBOL_ERROR        -> CLEAN
nogc_async_mut.js.engine.interpreter_async: SYMBOL_ERROR -> CLEAN
nogc_async_mut.js.conformance.runner: SYMBOL_ERROR       -> CLEAN
```

`src/app/js/main.spl` reported CLEAN pre-fix, but that result is **vacuous**:
the binary printed its usage banner and exited, so the function holding line 134
was never lowered. The direct discriminator probe above proves that file's
`JsValue` is Symbol-less, so its arm is the same defect, latent.

## Root cause and remaining scope (NOT done in this lane)

The proximate cause is that the `Symbol` arms were written against the `common/`
enum and copied into trees that use the Symbol-less one. The enabling condition
is the tier-less `use std.js.types.js_types` import, whose target is chosen by
directory-listing order — see
`doc/08_tracking/bug/tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md`
(stage 1 warning landed; stages 2-3 open).

Deliberately **not** attempted here, and recommended as follow-up:

1. **Make the JS imports tier-explicit.** ~20 files under
   `src/lib/nogc_sync_mut/js/`, plus `src/lib/nogc_async_mut/js/` and
   `src/app/js/`, import `std.js.types.js_types` tier-lessly. They should name
   their tier so resolution stops depending on listing order.
2. **Converge or clearly separate the three enums.**
   `src/lib/js/types/js_types.spl` and
   `src/lib/nogc_sync_mut/js/types/js_types.spl` are variant-identical and one is
   redundant. `common/js/types/js_types.spl` is a genuinely richer type (property
   descriptors + prototype chain) used by the bytecode/JIT VM in
   `src/lib/common/js/engine/`; it is a different contract, not a drifted copy,
   so it should be *renamed or namespaced*, not merged. Converging requires
   deciding whether the tree-walking engines adopt property descriptors — out of
   scope here.
