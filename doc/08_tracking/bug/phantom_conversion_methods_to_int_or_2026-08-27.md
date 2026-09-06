# Phantom conversion methods: `.to_int_or` / `.to_float_or` / `.to_i64_or` abort at runtime

- **Filed:** 2026-08-27
- **Class:** latent crash — call to a method with zero definitions anywhere in the tree
- **Rebased onto:** `f6ad97b10d9616a13bf6d450790361ca81cf9764` (origin/main)
- **Status:** 39 remaining live call sites fixed here; the 3 perf sites were
  already fixed on main by `9459cd74501`

## Summary

Simple code across `src/` calls conversion methods on `text` values that **do
not exist**. There is no definition in `.spl`, no `pub extern "C" fn` in the
Rust runtime, no `rt_*` in the C runtime, and no string-dispatch entry anywhere
in `src/compiler/`, `src/compiler_rust/`, or `src/runtime/`. The call parses and
type-checks, so the tree looks healthy; it aborts the moment the code path is
reached:

```
semantic: method `to_int_or` not found on type `str` (receiver value: 42)
semantic: method 'to_int_or' not found on value of type str in nested call context
```

This is not a missing feature. It is dead code that has never executed on these
paths, so any user reaching them gets an abort rather than a value.

## The phantom set

Six names were probed for definitions (`fn NAME`, `pub fn NAME`, and
string-dispatch mentions in the compiler/runtime trees). All six have **zero**
definitions:

| name | defs | verdict |
|---|---|---|
| `to_int_or` | 0 | **PHANTOM** — 36 live method call sites |
| `to_float_or` | 0 | **PHANTOM** — 5 live method call sites |
| `to_i64_or` | 0 | **PHANTOM** — 1 live method call site |
| `first_or_default` | 0 | **not phantom** — defined in-file by a trait in each spec that uses it (`trait_coherence_spec.spl:383,386`) |
| `unwrap_or_default` | 0 | **not phantom** — every hit is the lint rule `silent_default.spl` matching the name as a *string*, plus its own spec fixture. No call sites. |
| `force_or_default` | 0 | **suspected phantom, NOT fixed here** — 2 sites in `src/app/interpreter/lazy/lazy_val_spec.spl:105,112` on a `LazyVal` receiver. Different family (lazy values, not text conversion), out of this task's conversion/parse scope. Needs its own investigation. |

Note the free-function form `fn to_int_or(s: text, default: i64)` **does** exist
in three modules (`tmux/mod.spl:11`, `database/feature_utils.spl:152`,
`nogc_async_mut/mcp/main_lazy_debug_tools.spl:23` as `debug_to_int_or`). Those
are local workarounds, explicitly commented as "replacement for missing
`.to_int_or()` method", and are unaffected. Only the **method** form is phantom.

## Call sites

Census: `/usr/bin/grep -rn '\.to_int_or(\|\.to_float_or(\|\.to_i64_or('
src/ test/ --include=*.spl`, excluding vendored paths per CLAUDE.md's
Owned-Code Scope. Comment-only occurrences excluded. **42 live sites in 9
files; zero in `test/`.**

| file | sites | default | fix | status |
|---|---|---|---|---|
| `src/lib/nogc_sync_mut/test_runner/test_db_parser.spl` | 24 | `0` | `.to_int()` | FIXED |
| `src/lib/nogc_sync_mut/io/resource_scope.spl` | 8 | `0` | `.to_int()` | FIXED |
| `src/lib/nogc_sync_mut/io/resource_scope.spl:323` | 1 | `executed.usage.exit_code` | `try_parse_int(...) ?? default` | FIXED |
| `src/lib/gc_async_mut/gpu/browser_engine/script/js_compat.spl:63,73` | 2 | `0` / `0.0` | `.to_int()` / `.to_float()` | FIXED |
| `src/lib/nogc_sync_mut/src/infra.spl:111` | 1 | `0` | `.to_int()` | FIXED |
| `src/lib/nogc_sync_mut/test_runner/rust_test_runner.spl:89` | 1 | `-1` (sentinel) | `try_parse_int(...) ?? -1` | FIXED |
| `src/app/llm_caret/claude_full/bridge/bridgeMain.spl:449` | 1 | `0` | `.to_int()` | FIXED |
| `src/app/io/mod.spl:182` | 1 | `default` (f64 param) | explicit empty-output guard | FIXED |
| `src/app/perf/main.spl:31,52,89` | 3 | `0.0` | real float parsing | **FIXED on main by `9459cd74501`; no PR delta** |

`src/lib/nogc_sync_mut/tmux/mod.spl` was fixed earlier at `88fe280bb0f` (it now
uses the local free function) and needs nothing.

## Builtin behaviour (verified empirically, not assumed)

Probed with `bin/simple run` on the seed:

| expression | result |
|---|---|
| `"42".to_int()` | `42` |
| `"abc".to_int()` | `0` |
| `"".to_int()` | `0` |
| `"1.5".to_float()` | `1.5` |
| `"abc".to_float()` | `0.0` |
| `"".to_float()` | `0.0` |
| `try_parse_int("42") ?? -1` | `42` |
| `try_parse_int("abc") ?? -1` | `-1` |
| `try_parse_int("") ?? -1` | `-1` |
| `try_parse_int(" 7 ") ?? -1` | `7` (trims) |

So `.to_int_or(0)` -> `.to_int()` and `.to_float_or(0.0)` -> `.to_float()` are
exactly semantics-preserving. The three non-zero-default sites are not, and were
handled explicitly:

- `rust_test_runner.spl:89` — `-1` is a **sentinel**: the loop scans words until
  one parses, and `num >= 0` is the "did it parse" test. `.to_int()` fails open
  to `0`, which passes that guard, so the first non-numeric word would be
  returned as a count of zero. Uses `try_parse_int(...) ?? -1`.
- `resource_scope.spl:323` — the fallback is a real process exit code;
  failing open to `0` would report success for a failed unit. Uses
  `try_parse_int(...) ?? executed.usage.exit_code`.
- `app/io/mod.spl:182` — an `f64` default. `src/lib/common/convert.spl` has no
  float counterpart to `try_parse_int`, and adding one is out of scope (see
  below), so the guard is written inline at the single call site: `bc` only
  emits a number on exit 0, and the exit code is already checked, so the one
  divergent case is empty output, which is guarded explicitly.

## Should a `*_or` family exist?

Three modules independently wrote their own `to_int_or` free function, and the
comments in `test_config.spl:11,200` refer to a historical "`to_int_or` /
`parse_f64_or` fallback semantics", so the tree clearly *wants* this shape.
**Not implemented here** — out of scope per the task, and the perf fix now on main established
there is no such family to extend. If it is wanted, the right move is a single
`std.convert` pair (`to_int_or(s, default)`, `to_float_or(s, default)`) built on
`try_parse_int` / a new `try_parse_float`, plus deleting the three local copies.
A float counterpart to `try_parse_int` is the concrete missing piece:
`try_parse_float` exists only as a private helper at
`src/lib/nogc_sync_mut/src/exp/config.spl:598`.

## Reproduce specs

Each verified to fail pre-fix (by reverting only the source file) and pass
post-fix:

| spec | pre-fix | post-fix |
|---|---|---|
| `test/01_unit/browser/script/js_compat_spec.spl` (pre-existing, was RED on main) | 43/47, 3 phantom-method aborts | 48/49; all integer/float prefix, sign, whitespace, radix, invalid, and empty cases pass |
| `test/01_unit/app/tooling/test_db_parser_spec.spl` (extended) | 34/36, 2 aborts | 36/36 |
| `test/01_unit/lib/rust_test_runner_extract_count_spec.spl` (new) | 1/3, 2 aborts | 3/3 |

`js_compat_spec.spl`'s remaining failure (`date_now returns positive
timestamp`) is pre-existing and unrelated.

## Not covered by a spec

`resource_scope.spl`, `app/io/mod.spl`, `infra.spl` and `bridgeMain.spl` are
environment-dependent (systemd-run, `bc`, `/proc`, a live bridge) and have no
existing unit spec to extend. Their edits are mechanical
`.to_int_or(0)` -> `.to_int()` substitutions plus the two documented non-zero
guards. Standalone `bin/simple compile` on each was checked to be at **baseline
parity** — `resource_scope.spl`, `app/io/mod.spl` and `infra.spl` already fail
standalone compilation on pristine `origin/main` with `undefined identifier:
panic` (an artifact of compiling a library module in isolation), unchanged by
this work; `bridgeMain.spl` compiles clean before and after.

## Why no gate caught this

No existing check resolves method calls against a definition set. The linter's
`silent_default.spl` rule matches `.unwrap_or_default()` by *string*, which is
the closest thing in the tree and does not generalise. A ratchet in the shape of
`check-unbacked-extern-ratchet.shs` — but for method receivers on primitives —
would catch the whole class. Not implemented here.
