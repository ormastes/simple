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

| Operation | Native codegen result | Safe to use? |
|---|---|---|
| `d.len()` / `d.length()` | **-1**, always — local or struct field, empty or populated | **NO** |
| `d.get(k)` — **miss** | **zero VALUE of `V`, not `nil`** — `0` / `false` / non-nil text. `== nil` is **false**, `?? default` **never fires** | **NO** |
| `d.get(k)` — hit, `V` = `bool`, value `true` | reads `true` but `== nil` is **true** — a present key looks missing | **NO** |
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
  stored `0`.
- **Count** — never `d.len()`. For cold paths use `d.keys().len()`. For hot
  loops, maintain your own counter alongside the dict instead of recomputing
  a length.
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
