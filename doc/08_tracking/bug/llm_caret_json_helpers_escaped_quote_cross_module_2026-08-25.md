# `extract_json_string` drops the escaped-quote tail only under `simple test` — 2026-08-25

Status: CARET SPEC GREEN (workaround landed 2026-08-25); underlying seed
defect OPEN — it is the known name-keyed co-compile registry, tracked in
`doc/08_tracking/bug/co_compiled_symbol_collision_decision_2026-08-09.md`,
`compiler_cross_module_private_symbol_collision_2026-06-16.md`, and the
"fourth vacuity shape" in `vacuous_spec_census_2026-07-30.md` §Batch 1.

## Symptom (before)

`test/01_unit/app/llm_caret/json_helpers_spec.spl` —
`Results: 41 total, 40 passed, 1 failed`:

```
✗ extracts a string value containing an escaped quote
    expected say \ to equal say \"hi\"
```

## Root cause — NOT a lexer / escaped-literal defect (earlier theory retracted)

The earlier version of this record blamed a `"\\"` literal representation
mismatch across module boundaries. That is wrong. Classification: **(a)
seed defect, in module co-compilation, not the lexer.** (b) is ruled out:
a live source edit of the shadowing definition took effect immediately, so no
stale `.smf` is involved. (c) is ruled out: `json_helpers.spl:131-155` is
correct and runs correctly under `simple run`.

Mechanism: `src/app/llm_caret/json_helpers.spl` imported
`std.mcp.helpers.{Q, LB, RB, js, jp}`. `src/lib/nogc_async_mut/mcp/helpers.spl:135`
also defines `extract_json_string(json: text, key: text) -> text` (delegating
to `extract_json_string_v2`, which has NO backslash-escape tracking and so
stops at the first `"` after the opening quote — exactly `say \`). The seed's
module loader flattens every co-compiled module's free functions into a
registry keyed by bare NAME
(`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1504`, doc
comment: "The real fix is to key the registry on (module path, name) rather
than on the name alone"). `simple test` co-compiles the whole import closure,
so `std.mcp.helpers`' definition silently won over the imported one. The
same-signature case emits NO diagnostic unless
`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1` (`module_loader.rs:1543`); the
warning that did print — `extract_json_string has 3 co-compiled definitions
with 2 differing signatures` — is the differing-signature variant, triggered by
the third copy in `src/lib/nogc_sync_mut/mcp_sdk/core/json.spl:65`.

## Evidence

1. Minimal two-file probe (`/mnt/data/tmp/claude-1000/jh/{mod,main}.spl`:
   `mod.spl` defines `count_bs`/`extract`/`bs_lit` doing `ch == "\\"` over
   `text[i]`; `main.spl` imports them and compares against a local copy).
   Output is identical and correct in `SIMPLE_EXECUTION_MODE=interpreter` and
   `=jit` on `bin/release/x86_64-unknown-linux-gnu/simple`:
   `module_count=2 local_count=2 module_extract=say \"hi\" bs_lit_len=1
   bs_lit_eq_local=true`. So escaped literals do NOT differ across modules.
2. `/mnt/data/tmp/claude-1000/jh/real.spl` (`use
   app.llm_caret.json_helpers.{extract_json_string, jo1, escape_json_text}`,
   calls the real module) prints `out=say \"hi\"` under `simple run` in both
   modes and on the fresh seed in `/mnt/data/tmp/claude-1000/caret-clean`.
   Only `simple test` fails.
3. Sabotage (decisive): temporarily replacing the body of
   `std.mcp.helpers.extract_json_string` with `"SABOTAGE_HELPERS"` and running
   the caret spec gives `Results: 41 total, 37 passed, 4 failed` with every
   `extract_json_string` example reporting `expected SABOTAGE_HELPERS to equal
   ...` — the spec's imported call was being served by `std.mcp.helpers`.
   (Edit reverted; `git diff --stat` clean.)

## Fix (workaround in caret scope; seed defect stays open)

- `src/app/llm_caret/json_helpers.spl`: dropped the `std.mcp.helpers` import
  and defined the five one-liners (`Q`, `LB`, `RB`, `jp`, `js`) locally, so
  `std.mcp.helpers` is no longer in the spec's co-compile closure. No
  consumer imported those names from `app.llm_caret.json_helpers`.
- `test/01_unit/app/llm_caret/json_helpers_spec.spl`: replaced the stale
  `TODO(json-extract-hijack)` note with the confirmed cause; added similar-case
  examples: escaped quote before the closing quote, escaped backslash at end,
  double backslash mid-string, `é` unicode escape.

After: `Results: 45 total, 45 passed, 0 failed`, and the
`extract_json_string` co-compile warning is gone from the run.

## Unblock condition for the seed

Key the flattened function registry on (module path, name) per
`module_loader.rs:1504`, or make same-signature collisions fatal by default.
Until then any module that imports `std.mcp.helpers` (or any other module
carrying a same-named public function) gets its own definition hijacked under
`simple test`; the sabotage probe above is the reproduce recipe.
