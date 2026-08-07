# Dict Pitfalls Under Native Codegen

Two native-codegen defects make common `Dict` operations silently wrong or
crash-prone. They are **native-only** — the interpreter and the Rust seed
both behave correctly, so a seed build or an interpreter-mode test run
**cannot** catch either bug. Only a native build/run exercises the broken
paths. Treat "seed-build verified" or "interpreter test green" as no signal
at all for dict correctness.

Both syntaxes are affected: `Dict<K, V>` **and** the brace shorthand
`name: {K: V}`. A grep for `Dict<` alone misses roughly a third of the real
exposure — always also search for `: {`-style dict declarations.

## Truth table

> **UPDATED 2026-08-01.** Two rows changed. `.len()` no longer reproduces as
> `-1` — measured `2` for both a local `Dict<text,i64>` and a dict passed as a
> function parameter, on a native ELF built from `8fdc21c67b5`. And the
> `.get()` MISS row is now correct for `i64` and `bool` value types (fix:
> `dict_get_preserve_flat_nil`, see
> `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`).
> **`text`-valued dicts are still broken on a miss** — the `contains_key(k)` +
> `d[k]` replacement below is still mandatory for those.

> **RE-VERIFIED 2026-08-07 on the current working tree, real JIT execution
> (`bin/simple run`, Cranelift JIT — the native-codegen lane; see
> `.claude/rules/testing.md` "run and test are DIFFERENT ENGINES"; confirmed
> via `cranelift_jit::backend` log lines, not a silent interpreter fallback).
> `d.len()` (local + parameter), `.get()` hit for `i64`/`text`/struct, and
> `.get()` miss for `i64`/`text` (both `== nil` and `?? default`) all measured
> **correct**. The `text`-miss row above is now STALE: `guardable_value_type`
> at `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:991` already
> includes `mir_type_is_str`, so `dict_get_preserve_flat_nil` guards `text`
> the same way it guards integers — the "still broken" note predates that
> guard landing. Root cause for every row above, in one place: `rt_dict_get`
> (`src/runtime/runtime_native.c:7137`, flat-Option ABI) returns the nil
> sentinel `RT_NIL == 3` on a miss; `decode_runtime_value`
> (`expr_dispatch.spl:741`) has per-type arms that TRANSFORM the raw word
> (`>>3` for ints, `rt_interp_cstr` for text) and would destroy that sentinel
> on a miss; `dict_get_preserve_flat_nil` (`expr_dispatch.spl:833`) routes the
> sentinel around the transform via a branch-and-select, gated by
> `guardable_value_type` (`expr_dispatch.spl:991`, integer or str). Struct/
> enum/array/dict decode arms need no guard — their arm already passes the raw
> word through untouched, so nil survives for free.
>
> **One row is confirmed still genuinely broken: `.get()` miss for `V = f64`.**
> Reproduced live: `Dict<text, f64>` with one stored key, `.get()` on an absent
> key, `== nil` is **false**. This is not a stale doc gap — it's a *deliberate,
> commented* exclusion at `expr_dispatch.spl:987-990`: `guardable_value_type`
> (line 991) only matches `mir_type_is_integer` or `mir_type_is_str`; f64 is
> explicitly left out because `rt_value_as_float` cannot round-trip the `3`
> sentinel through a float bit pattern, and the flat `Option<f64>` ABI has no
> spare bits to carry a sentinel alongside a real float payload. Fixing this
> needs an ABI change (e.g. a boxed/side-channel discriminant for float
> Options), not a decode-arm guard — out of scope for a minimal fix. Tracked
> with the bool case in
> `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`.
> Spec coverage for both the fixed rows and this open gap:
> `test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl` (passes under the
> interpreter always — see that file's lane-coverage warning; the f64 case is
> not currently reproducible through the interpreter-only `bin/simple test`
> runner, only through `bin/simple run`).

| Operation | Native codegen result | Safe to use? |
|---|---|---|
| `d.len()` / `d.length()` | correct count since 2026-08-01 (measured: local **and** function parameter). The old **-1** does not reproduce; struct-field receivers remain unmeasured | yes for locals/params |
| `d.get(k)` — miss, `V` = `i64` / `bool` | correct `nil` since 2026-08-01 — `== nil` true, `?? default` fires | yes |
| `d.get(k)` — miss, `V` = `text` | correct `nil` — re-verified 2026-08-07 on current source (see re-verification note above); the row title below was stale | yes |
| `d.get(k)` — miss, `V` = `f64` | **confirmed broken 2026-08-07** — `== nil` is false; flat Option ABI cannot carry a sentinel in a float word; deliberately unguarded, see note above | **NO** |
| `d.get(k)` — hit, `V` = `bool`, value `true` | correct since 2026-08-01 (`.get()` on a bool dict now returns the raw 3-state word) | yes |
| `d.get(k)` — hit, `V` = `i64` / `text` | correct since `7e83e92ce314` (was `7`→`56`) | yes |
| `d.get(k)` — hit, `V` = struct/class/enum | correct since `7e83e92ce314` (was a segfaulting corrupt `Option`) | yes |
| `d.get(k).?` | **conflates a present `0` with empty** — reports empty for a stored zero | **NO** |
| `d[k]` indexed read — **miss** | **`0`**, silently — no miss signal at all | **NO** |
| `d.contains_key(k)` | correct | yes |
| `d.keys()` | correct | yes |
| `d[k]` indexed read — hit | correct | yes |
| `Some(d[k])` manual wrap | correct — round-trips through `.unwrap()` and `Option`-typed params | yes |

> **CHANGED 2026-07-28 — the MISS row was previously WRONG.** This table used to say
> `d.get(k)` on a miss was "correct, `nil`". It is not: a miss returns the **zero value**
> of the dict's value type, so a missing key is indistinguishable from a present zero.
> **Measured natively for `i64`, `bool`, and `text`** (standalone native ELF, no
> interpreter). Several 2026-07-27 sweeps reviewed call sites against the old
> "miss path is safe" assumption and **need revisiting**. Struct/class/enum value types
> were **not** measurable (any module-level `struct` makes native-build fail with
> `MIR module has no functions`); static reading says they preserve nil, but that is
> unverified. Details:
> `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`.
>
> Cause: `rt_dict_get` returns the nil sentinel `3` on a miss, and the MIR lowering
> decodes it as data with no nil guard — `3 >> 3` → `0` for integers, `3 == 11` → `false`
> for bools, `rt_interp_cstr(3)` → `NULL` for text. Only the struct/default decode arm
> passes the sentinel through untouched. This is **pre-existing**, not caused by
> `7e83e92ce314` — it was first sighted as `scratchpad/dict_native_report.md` item 15
> and never filed until now.

## Replacements

- **Membership check** — use `contains_key(k)`, never infer it from `.get(k) != nil`.
  A miss returns the zero value, so `.get(k) != nil` is **true for every key**,
  present or not.
- **Miss / default handling** — `.get(k) ?? default` and `val Some(x) = .get(k) else:`
  both take the present-value branch on a miss. Test `contains_key(k)` first and
  supply the default yourself. `.get(k).?` is also unsafe — it reports empty for a
  stored `0`. **Exception, re-verified 2026-08-07:** for `V = i64`, `bool`, or
  `text`, `.get(k)`'s miss handling (`== nil`, `?? default`) is correct on the
  current native/JIT lane — the guard above is still the right default for
  everything else (struct/enum/array/dict decode is unmeasured on a miss; `f64`
  is confirmed still broken).
- **Count** — `d.len()` is correct again as of 2026-08-01 for local and
  parameter receivers; the `d.keys().len()` workaround is no longer required
  for those, though it stays correct. Struct-field receivers have **not** been
  re-measured, so leave existing `keys().len()` calls on fields alone until
  they are.
- **Value fetch** — use `contains_key(k)` then index-read `d[k]`, not `.get(k)`.
- **Need an `Option`** — wrap the index read yourself: `Some(d[k])`, not `.get(k)`.

## Examples

BAD:

```simple
if d.len() == 0:
    return

val entry = d.get(name)
if entry != nil:
    print entry.unwrap().field
```

GOOD:

```simple
if d.keys().len() == 0:
    return

if d.contains_key(name):
    val entry = d[name]
    print entry.field
```

BAD (Option needed downstream):

```simple
val maybe: Tr? = d.get(key)
```

GOOD:

```simple
val maybe: Tr? = if d.contains_key(key): Some(d[key]) else: nil
```

## `.set()` conversion status (census 2026-07-31)

`.set()` is the write-side member of this family: it silently DROPS the insert
under native codegen. Always write `d[k] = v`.

Converted and landed: **35 sites** — `9d6527489f9d` (std.diag, 7) and
`e46120dfdf6c` (28 across 7 files). Evidence that `d[k] = v` is correct in the
interpreter is a sentinel probe on `diag_spec.spl`: 14/14 both before and after
the conversion, but 13/14 (`counter bytes_sent = 0`) when one converted write was
deliberately mis-keyed. That step matters — "green before and after" alone cannot
distinguish a correct change from a spec that never executes the line.

**The family is NOT closed. 71 verified builtin-`Dict` `.set()` sites remain**
across 19 files (12 under `src/`, the rest test-only). Highest-priority live
clusters: `security/types.spl` (12 — `keys`/`sessions`/`key_handles`/
`accepted_signatures`), `security/auth/context_propagation.spl` (12, three
concurrency-tier copies), `security/kms_provider.spl` (4),
`app/interpreter/core/environment.spl` (2 — `Scope.bindings`, the interpreter's
own variable define/set path).

**Do not grep-and-convert blindly.** A bare `.set(` sweep is overwhelmingly false
positives: `SdnRow` (744+ sites — its own `me set` already does `self.fields[k]=v`
internally), the `Persistent*` map/trie/set family (~1,000+, each with its own
`fn set`), array `[T].set(i, v)`, `Bitset`/`RowBitmap`/`FixedArray`, and a
*custom* `Map<K,V>` struct at `src/lib/nogc_sync_mut/src/map.spl` that is not a
builtin `Dict` at all. Resolve each receiver's declared type before touching it.

Two things found during the census that are NOT this bug:
- `src/app/ui.mcp/tools.spl:87` and `test/03_system/os/file_io_spec.spl:81` call
  `.set()` on `SdnDocument`, which has **no `.set` method** — stale callers
  against a refactored API.
- `src/compiler_rust/lib/std/**` holds ~54 more sites but is **dormant** (zero
  importers). Do not fix it; also do not delete it, as it carries unique Lean
  formalization files.

Reachability notes, so later readers don't over-rate two of the converted
clusters: `VhdlConstraintChecker`/`TarjanSCC` in `70.backend/vhdl_constraints.spl`
is **never constructed by the live `--backend vhdl` pipeline** — only by its own
unit spec. And `app/interpreter/helpers/imports.spl` is **entirely orphaned**: no
`.spl` file imports it, and its `Module__new` receiver has no `struct Module`
anywhere in live code (the real loader is `interp.load_module` in
`module/evaluator.spl`). Converting them was harmless, but neither was a live
production defect.

## Background

- `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md` —
  `.get()` on a MISS returns the zero value of `V` instead of `nil`; `== nil`,
  `??`, and `.?` all take the wrong branch. Silent wrong answer, no crash.
- `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md` —
  `.len()` always returns -1 under native codegen.
- `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
  — `.get()` on a hit returns a corrupt Option (struct values) or a
  still-boxed value (`i64` values).
- `doc/09_report/dict_get_struct_value_exposure_sweep_2026-07-27.md` — sweep
  of 193 CRITICAL call sites across the repo; documents the `Dict<`-only
  grep undercount.

These defects caused a multi-hour misdiagnosis during 2026-07-27 stage-4
bootstrap debugging: a `.len() < 0` guard was mistaken for a legitimate
signal, an unrelated `while d.len() < cap` loop ran unbounded, and a
`functions.len() < 0` "partial module" heuristic fired on every module.
