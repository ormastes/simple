# CoreLexer query helpers declared `fn`, not the `me` receiver the spec expects; a documenting comment is missing

- **Filed:** 2026-09-06
- **Status:** OPEN
- **Area:** compiler / frontend lexer — `src/compiler/10.frontend/core/lexer_struct.spl`
- **Spec:** `test/01_unit/compiler/lexer/core_lexer_receiver_capability_source_spec.spl`

## Symptom

`test/01_unit/compiler/lexer/core_lexer_receiver_capability_source_spec.spl`
has two RED scenarios, pre-existing before this modernization pass (baseline
`1 pass / 2 fail`, unchanged after modernizing the spec's structure/oracle
surface):

1. **"aliases only live-cursor query helpers and scratch-backed slicing"** —
   every one of the 13 listed cursor query helpers (`at_end`, `peek`,
   `peek_next`, `peek_at`, `word_boundary_at`, `measure_indent_from`,
   `skip_indent_from`, `line_starts_binary_op`, `leading_op_continues`,
   `char_slice`, `fs_nested_string_may_open`, `fs_expr_has_word`,
   `fs_expr_ends_with_word`) is declared with a plain `fn` in
   `lexer_struct.spl` (e.g. `fn at_end() -> bool:` at line 204, `fn peek() ->
   text:` at line 209), not the `me` receiver the spec asserts. `grep -c "    me "
   lexer_struct.spl` shows `me` is still used for the genuinely mutating
   methods (`advance`, `scan_string`, `next_token`, etc.), so the split
   between `me` and `fn` is intentional design, but the 13 read-only helpers
   this spec names now sit on the `fn` side of that split, not `me`.

2. **"documents why scratch slicing may alias an already copied local
   snapshot"** — the expected comment substring `"that caller has already
   made the value copy"` does not appear anywhere in `lexer_struct.spl`
   (`grep` returns zero matches). The rationale comment the spec quotes was
   removed or reworded at some point without the spec being updated.

## Two readings, unresolved

- Reading A: the source regressed — these 13 helpers used to be `me` and
  should be restored, because pinning "query helpers use the narrowest
  receiver capability" is exactly what this spec's `describe` block name
  claims to guard.
- Reading B: the source improved — declaring genuinely read-only cursor
  helpers as `fn` (immutable receiver) rather than `me` is a *tighter*
  capability than before, and the spec is the one that is stale.

Resolving this requires a design decision from whoever owns
`lexer_struct.spl`'s receiver-capability convention, not a mechanical fix —
so the spec was left RED with this note rather than "fixed" either by
loosening the assertion (which would launder Reading A) or by fixing the
source to match the old assertion speculatively (which would be an
unrequested behavior change).

## Unblock condition

- Whoever owns the CoreLexer receiver-capability convention decides which
  reading is correct.
- If Reading A: change the 13 helpers back to `me` in `lexer_struct.spl`.
- If Reading B: update the spec's expected receiver (`me` → `fn`) and rename
  the scenario/description away from implying `me` is required.
- Either way, the second scenario needs its own resolution: either restore a
  comment containing the literal substring `"that caller has already made
  the value copy"` near the `slice_parts` scratch-buffer code, or update the
  spec's expected substring to match the current (or a newly authored)
  comment.
