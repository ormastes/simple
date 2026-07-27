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
| `d.get(k)` — miss | correct, `nil` | yes |
| `d.get(k)` — hit, `V` = struct/class/enum | non-nil `Option`, **corrupt payload** — `.unwrap()` or a field read **segfaults** | **NO** |
| `d.get(k)` — hit, `V` = `i64` | still-boxed value (e.g. `7` reads back as `56` = `7<<3`) | **NO** |
| `d.contains_key(k)` | correct | yes |
| `d.keys()` | correct | yes |
| `d[k]` indexed read | correct | yes |
| `Some(d[k])` manual wrap | correct — round-trips through `.unwrap()` and `Option`-typed params | yes |

## Replacements

- **Membership check** — use `contains_key(k)`, never infer it from `.get(k) != nil`.
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

## Background

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
