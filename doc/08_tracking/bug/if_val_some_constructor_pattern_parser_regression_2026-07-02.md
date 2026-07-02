id: if_val_some_constructor_pattern_parser_regression_2026-07-02
status: OPEN
severity: high
discovered: 2026-07-02
discovered_by: bin/simple check on src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl
related: src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl
related: src/lib/nogc_async_mut_noalloc/replay/bm_checkpoint.spl
related: src/compiler/00.common/effects.spl
related: src/compiler/70.backend/backend/codegen_errors.spl
---

# `if val Some(x) = expr:` constructor-pattern binding fails to parse (self-hosted `bin/simple check`)

## Summary

The pattern-binding form `if val Some(<name>) = <expr>:` — used throughout
the codebase to conditionally unwrap an `Option<T>` — currently fails to
parse with the self-hosted `bin/simple` binary, everywhere it is used,
not just in the two sites originally reported.

```
[parser_error] line 52:16: expected =, got ( '('
```

The column points at the `(` right after `Some`, i.e. the parser accepts
`if val <ident>` (plain identifier binding) but does not accept
`if val <Ctor>(<ident>)` (constructor-pattern binding) in this build.

## Repro

```
fn bm_path_dirname(path: text) -> text:
    ...
    val last_sep = clean.rfind("/")
    if val Some(sep_idx) = last_sep:
        ...
    else:
        "."
```

```
$ timeout 180 bin/simple check src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl
[parser_error] line 52:16: expected =, got ( '('
[parser_error] line 68:16: expected =, got ( '('
```

## Not Isolated To This File

Confirmed the same failure on every file using this syntax that was spot
checked, including files far from the reported ones:

- `src/lib/nogc_async_mut_noalloc/replay/bm_checkpoint.spl:49` —
  `[parser_error] line 49:24: expected =, got ( '('`
- `src/compiler/00.common/effects.spl:115,119` —
  `[parser_error] line 115:20: ...` / `line 119:20: ...`
- `src/compiler/70.backend/backend/codegen_errors.spl:135,142,146` —
  `[parser_error] line 135:20: ...` / `142:20` / `146:20`

A repo-wide `grep -rn "if val Some(" src/` turns up dozens of call sites
across the compiler and stdlib; every one spot-checked with
`bin/simple check` on the current self-hosted binary reproduces the same
`expected =, got (` error. This means the short/canonical `if val Some(x) = expr:`
sugar is currently broken build-wide, not specific to the noalloc tier or
to `baremetal_path.spl`.

## Working Alternative (used as the workaround)

The equivalent `match` form parses cleanly and is already used elsewhere
in the same noalloc tier, e.g.
`src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl:181-186`:

```
match last_sep:
    Some(sep_idx):
        ...
    nil:
        "."
```

`bin/simple check` on `debug_boot_runner.spl` and on the rewritten
`baremetal_path.spl` (see below) both report zero parser errors.

## Applied Workaround

`src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl` — converted the
two `if val Some(...) = ...: / else:` sites (`bm_path_dirname` line ~52,
`bm_path_extension` line ~68) to the equivalent `match ...: Some(...): / nil:`
form. Verified `bin/simple check` on the file now passes with zero errors.

## Suggested Fix

Investigate the self-hosted parser's `if val <pattern> = <expr>:` grammar
rule (parser front-end, statement/if-let handling) for why a constructor
pattern (`Some(x)`, presumably also `Ok(x)`, `Err(x)`, other single-field
tuple variants) is not accepted as `<pattern>` after `if val`, while a bare
identifier is. Given the number of existing call sites relying on this
sugar, this should be treated as a parser regression rather than a
docs/style issue — either restore constructor-pattern support in `if val`,
or do a repo-wide migration to `match` if the sugar is being intentionally
removed.

## Citations

- `src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl:52,68` (original failure, now fixed)
- `src/lib/nogc_async_mut_noalloc/replay/bm_checkpoint.spl:49` (same failure, unfixed — out of scope for this task)
- `src/compiler/00.common/effects.spl:115,119` (same failure, unfixed — out of scope for this task)
- `src/compiler/70.backend/backend/codegen_errors.spl:135,142,146` (same failure, unfixed — out of scope for this task)
- `src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl:181-215` (working `match Some(...): / nil:` form used as the model for the workaround)
