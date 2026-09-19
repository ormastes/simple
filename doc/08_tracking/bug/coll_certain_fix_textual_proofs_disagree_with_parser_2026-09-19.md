# Textual safety proofs for the COLL Certain fix disagree with the parser

**Status:** FIXED 2026-09-19 on `work/coll-gaps` — all four proofs moved onto
the AST; the textual proof helpers are deleted, not merely bypassed.
**Severity:** Blocking — twelve `Certain`-confidence rewrites across two
review rounds turned working programs into wrong ones. `simple fix <file>`
needs no flag and writes in place.
**Affected files:** `src/compiler/35.semantics/lint/collection_patterns.spl`
(the proofs), `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`
(rendering only, from here on)
**Spec file:** `test/01_unit/compiler/lint/collection_certain_fix_safety_spec.spl`,
mirrored byte-identically at `test/unit/compiler/lint/`
**Predecessor:** `coll_certain_fix_rewrites_working_programs_wrongly_2026-09-19.md`
(round 1, five fixtures). This record is round 2 and supersedes that record's
*mechanism*: its fix was correct in intent and wrong in kind.
**Path:** `bug` track.

## The finding, stated as one defect rather than seven

Round 1 added four safety checks that read source text: a dominance scan that
looked for lines starting `"for "`/`"while "`, a block scan that ended at the
first line indented no deeper than its header, a mutation scan that walked
lines and matched `.method(` at token boundaries, and a freshness scan that
looked for an identifier in the file's text.

A review broke all four, seven more times:

| fixture | what text believed | original -> rewritten |
|---|---|---|
| `a1_while_paren` | `while(gi < n):` is not a loop header (no space) | `[1,2,3,4]` -> `[1,2,2,3,1,3,4]` |
| `a2_col0_comment` | a column-0 `# comment` ends the block | `[1,2,3,3]` -> `[1,2,3]` |
| `a3_tab` | a tab is indent 0 | `[1,2,3,3]` -> `[1,2,3]` |
| `a4_cont` | `val d = (seen` / `.pop())` is two statements | `[1,2,3,3]` -> `[1,2,3]` |
| `a5_named_arg` | `grow(k=x + 100, a=seen)` does not pass `seen` | `[1,2]` -> `[1,101,2]` |
| `a6_multiline_call` | `grow(` / `seen, x + 100)` does not pass `seen` | `[1,2]` -> `[1,101,2]` |
| `a8_for_shadow` | `for allowed in groups` is not a binding | `1` -> `0` |

These are not seven missing cases, and adding seven more text rules would
have produced an eighth review with an eighth list. Statement extent, block
extent, argument position and binding are all things the PARSER decides.
Any second opinion computed from characters is a guess that will eventually
disagree, and when it disagrees on a `Certain` rewrite the user gets wrong
code with no warning.

## Fix — the proofs live on the AST the detector already walks

`collection_fix_proofs(decl_indices) -> [CollectionFixProof]`
(`collection_patterns.spl`) returns every COLL002/COLL020 candidate in the
module, each marked `safe` or not, with the offending node's line for the
renderer. Nothing in it reads a line, trims a string or counts an indent.

| proof | AST form |
|---|---|
| **Site containment** | candidates are collected FROM a loop's body statement list, so "inside the innermost loop" is structural, not a line range |
| **Dominance** | `decl_sibling_before`: the declaration must be a `val`/`var` statement in the SAME statement list as the loop, at an earlier position. Sibling order is the parser's answer to "does this dominate" |
| **Whole-function mutation** | `stmts_have_unsafe_use` / `expr_has_unsafe_use`: a mutating method call on the name, an assignment to it or through its index, its appearance anywhere inside a call's ARGUMENTS (so named and line-split arguments are the same node), or capture by a lambda. Only the one kept-in-step push is exempt |
| **Name freshness** | `collection_module_names`: every identifier the module binds or mentions, from the AST. `{receiver}_set`..`_set10`, else refuse |
| **Shadowing** | `count_bindings_of` counts `val`/`var`/**`for`** bindings. A name bound more than once in a function is refused outright, which is what `a8_for_shadow` needed |

`entry_and_fixes.spl` now only RENDERS: byte offsets, the element-type
annotation to copy into `Dict<T, bool>`, the exact substring replaced. It is
handed the proven sites; it can only refuse further, never admit. Its leading
whitespace is copied verbatim (`collection_ws_prefix`, spaces AND tabs)
instead of counted.

The round-1 textual helpers (`collection_is_mutation_of`,
`collection_range_mutates`, `collection_decl_dominates_loop`,
`collection_function_mutates_outside`, `collection_line_mutates_name`,
`collection_rest_is_mutation`, `collection_fresh_identifier`,
`collection_ident_occurs_in_line`, `collection_is_mutating_method_name`,
`collection_name_passed_as_call_arg`, `collection_referenced_between`,
`collection_enclosing_loop_line`, `collection_enclosing_fn_start`,
`collection_block_end`, `collection_unique_line_containing`,
`collection_decl_element_type`) are **deleted**, not left for someone to
reuse. `collection_020_fix`/`collection_002_fix` are now thin wrappers that
parse and delegate, so no caller can reach a renderer without a proof.

## Nothing demoted to warning-only

Every one of the four proofs was expressible on the AST as it stands, so
nothing had to be approximated or dropped. The one thing the AST does NOT
carry is the SOURCE TEXT of a type annotation or a `.contains()` argument;
those are read back off the proven line for rendering and, failing that, the
fix is refused. That is not a safety decision — a mis-read there produces no
fix, never a wrong one.

A shape that fails any proof is reported by lint as a warning with no fix
attached, which is the intended outcome: every fixture in the table above
still prints `warning[COLL020]` / `warning[COLL002]`, verified.

## Verification — real CLI, all runs from `/home/yoon/dev/simple-coll-gaps`

Running `bin/simple fix` from outside the lane worktree resolves `src/` from
`/home/yoon/dev/simple` and reports "No fixes available" for everything, so
every verdict below was produced with `cd` into the lane first and `pwd`
echoed alongside it. The control (`fx/coll020.spl`) offers a fix in the same
session, which is what proves the runs were not vacuous.

```
control coll020.spl  ->  [COLL020] ... `out_set` ...
round 1: nested / outer_mut / pop_expr / coll002_pop   ->  No fixes available
         setname_clash  ->  [COLL020] ... `seen_set2` ...   (1 -> 1, proven)
round 2: a1_while_paren / a2_col0_comment / a3_tab / a4_cont /
         a5_named_arg / a6_multiline_call / a8_for_shadow
                                                       ->  No fixes available
lint on a1 / a2 / a8 / nested / pop_expr  ->  warning[COLL020|COLL002] kept
```

Still fixed, each A/B'd by execution: `coll020` `[3,1,2]`,
`coll020_two_array` `[3,1,2]`, `coll002_fixable` `[1,5,2]`, `whileidx`
`[1,2]` — identical before and after.

## Two spec expectations flipped, both because text left the picture

- **a09 "tab-indented file stays no-fix"** was never a safety property. It
  held only because `collection_line_indent` measured tabs as indent 0 — the
  same mis-measurement that corrupted `a3_tab`. It now fixes, and the spec
  asserts the emitted lines are tab-indented; verified by execution, `2` ->
  `2`.
- **T3 in `collection_two_array_dedup_spec`** asserted that the RAW textual
  generator still accepted an early `break`, as a tripwire on two layers
  drifting apart. There is no second layer any more, so that half is gone;
  the example still asserts no fix is offered.

## Pre-existing failure, verified not ours

`lint_parsed_revision_entry_spec` example "preserves parser state while
consuming matching declarations" fails (`expected 1 to equal 0`, a
LINTREV001 from an arena-generation mismatch). Reproduced identically with
this lane's two source files reverted to `84a3c865853` AND to the lane base
`7c875a81067`, so it predates the lane entirely.
