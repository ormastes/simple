# Seed binary cannot parse multi-line list literal in driver_compile_options.spl

Date: 2026-11-15
Status: verification-pending

## Symptom
Specs that compile `src/compiler/00.common/driver_compile_options.spl` end with
`outcome=ERROR ... executed=0` and:

    error: compile failed: parse: in src\compiler\00.common\driver_compile_options.spl:
    Unexpected token: expected RBracket, found Comma at line 63, column 31

Line 63 is the first line of a list literal that continues on the next line:

    ["target_profile_schema=1", "target_profile=" + mode,

## Confirmed on unmodified code
Run from C:/dev/wt/rb2-libunits (an ancestor of origin/release/1.0.0, no diff
for `src/compiler/00.common` or the spec vs origin/release/1.0.0):

    C:/dev/simple/bin/simple.exe test test/05_perf/compiler/mir_canonical_type_reverse_lookup_spec.spl
    -> SPEC FILE VERDICT: ... outcome=ERROR declared>=6 executed=0 passed=0 failed=0

Also reproduces on work/rb2-parity-20261115 for
test/01_unit/compiler/driver/native_mir_selective_worker_spec.spl
(`outcome=ERROR ... reason=parse-error`). Not caused by the
`next_canonical_type_symbol` removal (those edits only deleted expectation lines).

## Affected specs (at least)
- test/05_perf/compiler/mir_canonical_type_reverse_lookup_spec.spl
- test/01_unit/compiler/driver/native_mir_selective_worker_spec.spl

## Binary identity
    -rwxr-xr-x 1 user 197121 37622272 Nov 13 13:29 C:/dev/simple/bin/simple.exe
    Simple Language v1.0.0-rc.1
    (prints: "this Rust-built Simple binary is a bootstrap seed only")

## Fix direction
Either the seed parser must accept a list literal whose elements continue
across a line break after a comma following a binary expression, or the source
must be reformatted. Per CLAUDE.md, fix the parser (or record), do not silently
reformat the source as a workaround. Re-run both specs once resolved.

## Resolution (2026-11-16, lane rb4-seedlist)
Root cause: the bare list after `val x = match ...:` was parsed as an index
postfix on the last arm value. Already fixed in seed source by `eb9ed832623`
(`previous_ends_line` guard in `parser/src/expressions/postfix.rs`), which
postdates the deployed Nov-13 `bin/simple.exe`. Needs a seed redeploy.
Verified with a seed built from release/1.0.0 (own CARGO_TARGET_DIR, clang-cl):
- `cargo test -p simple-parser --test bare_collection_after_match_val`: 8 passed
  (4 new: multi-line continued list, trailing comma, nested list, call arg).
- `test/01_unit/compiler/parser/multiline_list_after_match_spec.spl`:
  deployed seed = parse error (`expected RBracket, found Comma`, line 13);
  new seed = `outcome=OK executed=4 passed=4`.
- `test/05_perf/compiler/mir_canonical_type_reverse_lookup_spec.spl` now
  executes 6 (was 0); its 4 failures are symbol-id value assertions, not parse.
Pure-Simple parser: postfix `[` path (`parser_expr.spl` parse_postfix_on) was
not runtime-verified (no full-CLI pure-Simple binary deployed).
