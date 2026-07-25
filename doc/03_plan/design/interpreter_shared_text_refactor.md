# Interpreter Shared Text Refactor Plan

## Scope

One coherent Rust seed-interpreter representation migration. No Simple grammar,
native runtime ABI, serialization schema, symbol representation, or GUI/WebIR/
DrawIR change.

## Lanes

- Spark discovery: 925-use/102-file impact inventory and mechanical ordering.
- Spark test: semantic, identity, Unicode, bridge, RSS, and parser gates.
- Merge owner: `/root`.
- Final reviewer: `higher_source_review`.

## Steps

1. Add `SharedText`, `Value::text`, and fail-fast clone/alias tests.
2. Change `Value::Str` and manual `Clone`, then add `Value::shared_text` in that
   same coherent step; update the executor characterization to require map COW
   but shared source identity.
3. Fix key/display/equality and the sole in-place concat owner; transformations
   produce new text and never mutate a shared Arc.
4. Fix Unicode index/slice and runtime/value bridge byte conversions.
5. Mechanically convert constructor sites; let Rust compile errors identify
   true owned-String boundaries. Do not blanket-clone borrowed strings.
6. Run each focused gate once, then one workspace compiler check/test.
7. Before migration, record max RSS in
   `doc/09_report/perf/interpreter_shared_text_rss_baseline_2026-07-13.md` with
   the exact `/usr/bin/time -v` commands in the architecture doc. Use the parser
   fixture and `test/fixtures/interpreter_shared_text_rss/main.spl`, which holds
   many distinct short strings. After migration, repeat identical commands;
   each max RSS must be <=110% of its own baseline. The parser's existing
   27.631s remains the timing baseline.
8. Add a source/test audit rejecting `Arc::make_mut`/`Arc::get_mut` on
   `Value::Str`, then run the 11/22 KiB parser oracle once. Only a full PASS
   permits bootstrap.

## Stop Conditions

- Stop at the first semantic or bridge regression.
- Maximum three compile/fix cycles; report remaining grouped errors.
- No parser scaling rerun before the representation materially changes.
- No 493-source shard unless 22 KiB is under 15s.

## Rollback

Revert the entire shared-text representation change together. Preserve the
independent lexer-source cache, Unicode offset correction, and global indexed
mutation fixes.
