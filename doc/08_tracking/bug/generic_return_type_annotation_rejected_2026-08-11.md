# Generic return-type annotation reported rejected — NOT REPRODUCIBLE (2026-08-11)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Report

Reported: the seed parser rejects generic return-type annotations —
`fn f() -> Result<i64, text>:` fails with `expected expression, found Lt`
(observed 2026-08-11).

## Investigation

Built a fresh seed from origin's live tip at investigation time
(`9809e69df6`, "fix(compiler): sync `.unwrap()` test assertions to
rt_unwrap_or_trap, chmod +x native-unwrap check"):

```
CARGO_TARGET_DIR=/mnt/data/cargo-target-parse cargo build --release --bin simple
# -> /mnt/data/cargo-target-parse/release/simple, built 2026-08-11 04:27
```

### Truth table (fresh seed, `simple compile`/`simple run`)

| form | position | result |
|---|---|---|
| `-> Result<i64, text>` | return | **compiles clean**, runs correctly (`Ok`/`Err` match works) |
| `-> Option<i64>` | return | compiles clean |
| `-> List<i64>` | return | compiles clean |
| `-> Result<List<i64>, text>` (nested) | return | compiles clean, runs correctly |
| `-> Result<Option<i64>, text>` (nested, double `>`) | return | compiles clean, runs correctly |
| `-> Result<i64, text>` on a class method (`fn bar(self) -> ...`) | return | compiles clean |
| `x: Result<i64, text>` | parameter | compiles clean (control) |
| `val v: Result<i64, text> = Ok(1)` | val decl | compiles clean (control) |

No case produced `expected expression, found Lt` or any other parse error.
The exact reported form, standalone, with `simple compile`:

```
$ cat exact.spl
fn f() -> Result<i64, text>:
    pass
$ simple compile exact.spl
Compiled exact.spl -> exact.smf
```

Ran end-to-end (interpreter fallback lane, since the seed's JIT always
falls back to the interpreter for user modules) with a `match` on the
`Result` payload — `Ok(1)` unwraps and prints `1`, nested
`Result<List<i64>, text>` unwraps to `[1, 2, 3]`.

### Tree evidence

`grep -rn -- '-> [A-Z][A-Za-z0-9_]*<' --include=*.spl` on `src/compiler` and
`src/lib`:

- `src/compiler`: 939 hits
- `src/lib`: 6,569 hits

e.g. `src/compiler/85.mdsoc/security.spl:322`:
`fn validate_security_dimension(dim: DimensionDef) -> Result<bool, text>:`,
and `src/lib/sdn/__init__.spl:7`: `fn parse_file(path: text) ->
Result<SdnValue, text>:`. This form is used pervasively across the owned
tree today, which is strong evidence it already works and is not a form
that "never worked" — a parser-level rejection of this shape would break
thousands of existing call sites, not just a hypothetical new one.

There is also a pre-existing spec pinning single-parameter generic return
types: `test/01_unit/compiler/frontend/unknown_generic_return_type_spec.spl`
(`-> List<text>`). This investigation adds a sibling spec for the
multi-parameter (`Result<T, E>`) and nested-generic cases:
`test/01_unit/compiler/frontend/multi_param_generic_return_type_spec.spl`.

## Root cause

None found — not reproducible. `src/compiler_rust/parser/src/parser_impl/functions.rs`
already routes the return-type position through `self.parse_type()` (both
function-declaration call sites, lines ~109 and ~501), the same type-parsing
entry point used for parameter and `val` type annotations, so there is no
"return position parses an expression instead of a type" code path to fix.

Possible explanations for the original report (none confirmed): a stale or
differently-configured deployed binary at observation time, a `bin/simple`
symlink pointing at an older build (see
`reference_bin_simple_symlink_stale_scratch_build_and_verify_binary_provenance.md`
in memory), or a since-landed adjacent fix (the postfix.rs `LParen`
adjacency fix mentioned as "yesterday's adjacent find" landed before this
investigation's build) that transitively resolved it.

## Guard added

`scripts/check/check-generic-return-type-parse.shs` — compiles 6 generic
return-type/parameter/val forms against `$SEED` (default
`bin/seed/simple`), verdict convention: `PASS — <n> case(s) checked, 0
rejected` (exit 0) / `FAIL — <n> of <n> case(s) rejected...` (exit 1) /
`ERROR — nothing was checked` (exit 2, e.g. missing binary). Verified
passing against the fresh seed build: `PASS — 6 generic-return-type case(s)
checked, 0 rejected`.

## Status

**Closed as not reproducible.** No code change to
`src/compiler_rust/parser/` was made — there is nothing to fix. If this
resurfaces, capture `bin/simple --version` / `readlink -f bin/simple` /
binary mtime at the time of the failure, since a stale deployed binary is a
recurring false-positive source in this repo (see MEMORY.md "Measurement
traps").
