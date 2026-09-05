# Tier-less `use std.js.*` resolves to `src/lib/js/`, never to the importer's own tier

Status: PARTIALLY FIXED (common/js/** made tier-explicit; other trees still exposed)
Date: 2026-08-01
Related: `tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md`
Related: `js_value_symbol_variant_alien_to_nogc_js_engines_2026-08-01.md` (commit `fde7f791f5b`)

## Summary

A tier-less `use std.js.<path>` does **not** resolve by directory-listing order,
and it does **not** prefer the importing file's own tier. When
`src/lib/js/<path>.spl` exists it wins deterministically, from every importer
location. When it does not exist, the tier search runs in a fixed order that
places `nogc_sync_mut` **before** `common`.

The practical effect: every file under `src/lib/common/js/**` that used a
tier-less import was silently loading a *different* module than the one beside
it — `src/lib/js/types/js_types.spl` for `js_types`, and
`src/lib/nogc_sync_mut/js/engine/*` for eight engine modules.

## Mechanism (PROVED, by code read)

`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`,
`_resolve_module_path_uncached`:

- `std.js.types.js_types` becomes relative path `lib/js/types/js_types.spl`.
- Step 1 (dir of the importing file) misses.
- Step 3 tries `src/` + relative path -> `src/lib/js/types/js_types.spl`, which
  **exists** -> returns.
- Step 4, the tier search, is never reached.

Step 4's order, when step 3 misses, is
`nogc_async_mut, nogc_async_immut, nogc_sync_immut, nogc_sync_mut, common, ...`
so `common` is reached only after `nogc_sync_mut` has been tried.

Note that three different components carry three different tier orders:
`module_loader_resolve.spl:214+`, `module_lowering.spl:677`, and
`99.loader/module_resolver/resolution.spl:262`. Only the last one lists
`common` first, and it is used for the ambiguity warning map, not for
resolution.

## Measurement (PROVED, non-vacuous)

A distinct sentinel `WHICH_JS_TYPES()` was appended to each of the three
`js_types.spl` files in a tmpfs copy of the tree, and a probe placed in each
candidate importer directory.

Tier-less `use std.js.types.js_types`, by importer location:

| importer directory | resolved |
|---|---|
| `src/lib/common/js/engine/` | `ROOT_js` |
| `src/lib/nogc_sync_mut/js/engine/` | `ROOT_js` |
| `src/lib/gc_async_mut/js/engine/` | `ROOT_js` |
| `src/lib/gc_async_mut/js/conformance/` | `ROOT_js` |
| `src/lib/gc_async_mut/web/` | `ROOT_js` |
| `src/lib/gc_async_mut/gpu/browser_engine/script/` | `ROOT_js` |
| `src/lib/nogc_async_mut/js/engine/` | `ROOT_js` |
| top-level (test-like) | `ROOT_js` |

Non-vacuity control — the same harness reports the other two values when the
import is tier-explicit:

| import | resolved |
|---|---|
| `std.common.js.types.js_types` (from `common/js/engine/`) | `COMMON` |
| `std.common.js.types.js_types` (from `gc_async_mut/js/engine/`) | `COMMON` |
| `std.nogc_sync_mut.js.types.js_types` (from `gc_async_mut/js/conformance/`) | `NOGC_SYNC_MUT` |

RED -> GREEN on real production code: a probe function appended to
`src/lib/common/js/engine/gc.spl` (a file that matches `JsValue.Symbol(_)` at
line 368) reported `ROOT_js` with the original tier-less import and `COMMON`
after the import was made tier-explicit.

## Why this matters

`src/lib/common/js/**` is the bytecode/JIT VM and it genuinely requires the
richer contract:

- `common/js/types/js_types.spl` declares `JsValue` with **9** variants,
  including `Symbol(id: i64)`; `JsProperty` with `key, value, writable,
  enumerable, configurable`; `JsObject` with `id, properties, prototype_id`.
- `src/lib/js/types/js_types.spl` and
  `src/lib/nogc_sync_mut/js/types/js_types.spl` declare **8** variants (no
  `Symbol`), `JsProperty{key, value, enumerable}`, `JsObject{properties}`.

`common/js/engine/vm_object_store.spl:277` builds
`JsObject(id:, properties:, prototype_id:)` and line 257 builds the five-field
`JsProperty` — neither is constructible against the root/`nogc_sync_mut` form.
Yet its import was tier-less, so it was loading the poorer type.

## Correction to the previous assessment

`fde7f791f5b` recorded that "the tier-less path currently resolves to a
Symbol-less enum" and listed `common/js/**`'s `JsValue.Symbol` uses as
legitimate. The first half is right; the second half does not follow. Those
`common/js/**` files were themselves resolving to the Symbol-less root enum.
They are the *broken* set, not the safe set. The fix is to give them the tier
they require, not to remove `Symbol`.

## Fix applied here

All 52 tier-less `use std.js.*` import lines under `src/lib/common/js/**` whose
target exists under `src/lib/common/js/` were rewritten to `std.common.js.*`
(30 files, import lines only, no other edits). This removes the resolution-order
dependency for that tree and gives it its own `js_types`, `ast_types`, `pair`,
`json`, `js_error`, `lexer`, `parser`, `runtime`, `interpreter_types`,
`vm_object_store`, and node modules.

One line is deliberately left tier-less:
`common/js/conformance/report.spl:4` imports `std.js.conformance.runner`, which
has no `common/` copy. It currently lands in `nogc_async_mut`. Deciding its home
needs a separate call.

## Still open

- `src/lib/gc_async_mut/js/**` has no `types/` of its own and still imports
  tier-less. `gc_async_mut/js/engine/interpreter_async.spl:575` and
  `gc_async_mut/js/conformance/runner.spl:91` match `JsValue.Symbol`, as do
  `gc_async_mut/web/browser_session_storage.spl:144` and
  `gc_async_mut/gpu/browser_engine/script/script_runner.spl:53`. These are the
  structural twins of the `nogc_async_mut` files fixed in `fde7f791f5b` and were
  missed there. The right fix is a tier decision for that tree, not another arm
  deletion — see the correction above.
- Roughly 20 spec files under `test/**` import tier-less and reference
  `JsValue.Symbol`; they resolve to `ROOT_js` and need the same tier decision.
- 574 tier-less `use std.js.*` lines across 177 files remain tree-wide.

## Oracle caveat for whoever picks this up

At tip `942fffb`, no available binary detects a missing enum variant or a wrong
field set:

- `bin/release/x86_64-unknown-linux-gnu/simple` has lost `run`/`build`/`check`/
  `lint`; only `compile --format=smf` remains, and it crashes with
  "field access on nil receiver" on a three-line probe.
- The Rust seed accepts `JsValue.Symbol(id: 7)` against the 8-variant enum and
  accepts the five-field `JsProperty` against the three-field class — a global
  name registry satisfies both. A discriminator probe stayed GREEN in all five
  configurations tried.

The `fde7f791f5b` evidence ("five modules went SYMBOL_ERROR to CLEAN, an
untouched discriminator probe stays RED") could not be reproduced here. Use the
sentinel-resolution oracle described above instead: it observes which *file* is
loaded and does not depend on any validation the toolchain may or may not
perform.
