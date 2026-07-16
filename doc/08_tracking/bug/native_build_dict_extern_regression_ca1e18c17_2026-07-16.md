# Bug: native-build broken under deployed seed since ca1e18c1744 (dict-extern migration)

**Status (2026-07-16):** Open. Blocks `scripts/check/native-smoke-matrix.shs`
(15/15 FAIL at 8ac25987333) for every lane using the deployed binary.

- **Severity:** P1 (the default tooling path `bin/simple native-build --entry`
  fails for ANY source with `error: semantic: type mismatch: cannot convert
  dict to int`)
- **First bad commit:** `ca1e18c1744` "wip(os): checkpoint memory leveling
  native verification" (bisect-proven via `git bisect run` between good
  `6456be19e64` and bad `8ac25987333`; probe = trivial two-function program,
  expected rc=42).

## Symptom

`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`
fails right after `[native-build] Driver start: ...` with
`error: semantic: type mismatch: cannot convert dict to int` (message format
matches the seed interpreter's `value_impl.rs as_int`). Reproduces with the
deployed 2026-07-11 seed binary interpreting the pipeline live, in the main
WC, in a clean worktree at 8ac25987333, and from an empty cwd.

## Root-cause direction

`ca1e18c1744` migrated pipeline code to `rt_dict_keys` / `rt_dict_values` /
`rt_dict_contains` externs (declared `dict: i64` in
`src/compiler_rust/lib/std/src/alloc/sffi.spl`) and simultaneously added the
seed-side support (`interpreter_sffi.rs`, `runtime_symbols.rs`,
`runtime/src/value/dict.rs`). The deployed 2026-07-11 seed predates that
support, so some dict-extern call site in the interpreted pipeline coerces a
Dict value through `as_int`. Reverting all `.spl` files touched by
ca1e18c1744 restores a working native-build at 8ac25987333; neither half of
the file list alone is sufficient (multi-file interaction), and
`driver_aot_output.spl` or `sffi.spl` alone are not sufficient either.

## Fix options

- Redeploy a seed built at/after ca1e18c1744 (its own compiler_rust changes
  include the needed extern support), or
- Make the `.spl` pipeline's dict-extern usage backward-compatible with the
  deployed seed (guard/fallback to `.keys()`/`.values()`/`.has()`).

## Regression gate

`sh scripts/check/native-smoke-matrix.shs` must return
`total=15 pass=15 fail=0` with the deployed binary.
