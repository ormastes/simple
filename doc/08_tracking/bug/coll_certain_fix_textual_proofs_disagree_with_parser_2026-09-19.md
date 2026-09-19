# Textual safety proofs for the COLL Certain fix disagree with the parser

**Status:** FIXED 2026-09-19 on `work/coll-gaps` — all four proofs moved onto
the AST; the textual proof helpers are deleted, not merely bypassed.
**Severity:** Blocking — sixteen `Certain`-confidence rewrites across three
review rounds turned working programs into wrong ones. `simple fix <file>`
needs no flag and writes in place.
**Affected files:** `src/compiler/35.semantics/lint/collection_patterns.spl`
(the proofs), `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`
(rendering only, from here on)
**Spec file:** `test/01_unit/compiler/lint/collection_certain_fix_safety_spec.spl`,
mirrored byte-identically at `test/unit/compiler/lint/`
**Predecessor:** `coll_certain_fix_rewrites_working_programs_wrongly_2026-09-19.md`
(round 1, five fixtures). This record covers rounds 2 and 3 and supersedes that record's
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
| **Whole-function mutation** | `stmts_have_unsafe_use` / `expr_has_unsafe_use`: ANY method call on the name whose method is not a proven reader, a call whose receiver merely MENTIONS the name (`seen[0].push`, `seen.field.push`, `f(seen).push`), an assignment to it or through its index, its appearance anywhere inside a call's ARGUMENTS (so named and line-split arguments are the same node) or inside an aggregate literal, or capture by a lambda. Only the one kept-in-step push is exempt |
| **Name freshness** | `collection_module_names`: every identifier the module binds or mentions, from the AST. `{receiver}_set`..`_set10`, else refuse |
| **Shadowing** | `count_bindings_of` counts `val`/`var`/`lazy val`/`bind`/**`for`**/`static for` bindings across every child statement list. A name bound more than once in a function is refused outright, which is what `a8_for_shadow` needed |
| **Inspectability** | `coll_stmts_inspectable`: a statement kind whose child lists this analysis does not enumerate, or a binding whose name is not a single plain identifier, makes the whole function uninspectable and downgrades every candidate in it to unsafe |

## Round 3 — the AST was right, the DEFAULTS were still inverted

The table above describes the code as it stands. It did not when first
written: a review broke the round-2 proofs four more ways, and all four were
one defect — the proofs were ALLOW-lists over enumerated cases, so anything
not enumerated defaulted to *safe*. The claims "a mutating method call
anywhere in the function" and "`count_bindings_of` counts val/var and for"
were, as written, false of the code.

| fixture | what the enumeration missed | original -> rewritten |
|---|---|---|
| `b1_else_mut` | only `stmt_get_body(if)` (the then-branch) was walked, so `seen.pop()` in an `else` was invisible | `[1,2,1,3,3]` -> `[1,2,3]` |
| `b1b_elif_mut` | same, via `elif` | `[1,2,1,3,3]` -> `[1,2,3]` |
| `b1c_else_coll002` | same, COLL002 side: `allowed.pop()` in an `else` | `[1,2]` -> `[1,2,3,1]` |
| `m_fill` | the mutating-method list was a whitelist; `fill` is a real runtime mutator that was not on it | `[1,2,1,2]` -> `[1,2]` |
| `b11c_var_destructure` | `var (seen, k) = ([], 0)` was not counted as a binding | `[1,1,2]` -> `[1,2]` |
| `b8b_nested_elem` | `seen[0].push(7)` has an EXPR_INDEX receiver, so it read as a call on nothing | `1` -> `3` |

What changed, with the measured facts that made each necessary:

- **Generic traversal.** `coll_stmt_child_stmts` returns every child
  statement list a kind owns — `else` bodies, match/receive arm bodies, loop
  and block bodies, defer/comptime/labelled-loop bodies — and
  `coll_stmt_child_exprs` adds an assignment's value (it lives in the body
  slot, not `stmt_get_expr`) and arm patterns/guards. Every walker uses them,
  so a kind added later is covered by construction. Two traps measured by
  probe, not assumed: `stmt_get_type` on an `if` is the elif RECORD index and
  is always `>= 0` — `0` for a plain `if` — so it is not a "has else" signal
  (testing it refused every guard, including the control); and
  `elif_get_body`/`elif_get_cond` MIRROR the then-branch and condition, so
  including them double-counted bindings and made one `known.contains(x)`
  look like two COLL002 candidates, which the ambiguity rule then refused.
  Only `elif_get_else` is taken from the record, exactly as
  `ast_traversal.spl` says.
- **Unknown kinds fail closed.** `coll_stmt_kind_known` enumerates the kinds
  handled; anything else makes the function uninspectable and every candidate
  in it unsafe. Downgraded rather than dropped, so a sibling function's safe
  proof cannot look like the file's only candidate.
- **Readers, not mutators, are listed.** `is_readonly_collection_method`
  admits `contains`/`len`/`get`/… and everything else on the tracked array is
  a mutation. `sort` and `reverse` are deliberately absent. Omitting a reader
  costs a suggestion; omitting a mutator cost correctness.
- **Binding names must be plain identifiers.** Destructuring does not produce
  an empty name as first assumed — `var (seen, k) = ([], 0)` yields the
  literal `"(seen,k)"` — so the emptiness test missed it. Anything that is
  not `[A-Za-z_][A-Za-z0-9_]*` makes the function uninspectable.
- **A guard with an `else`/`elif` is refused** for the fix (lint still warns):
  that branch runs when the value WAS present and the rewrite says nothing
  about it.

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

## Round 3 verification — real CLI, all runs from `/home/yoon/dev/simple-coll-gaps`

```
controls (must fix):
  coll020            [COLL020] ... `out_set`
  coll020_two_array  [COLL020] ... `seen_set`
  coll002_fixable    [COLL002] hoist `known`
  whileidx           [COLL020] ... `seen_set`
round 3 breaks (must refuse):
  b1_else_mut / b1b_elif_mut / b1c_else_coll002 / m_fill /
  b11c_var_destructure / b8b_nested_elem        ->  No fixes available
rounds 1-2 (12 fixtures) re-run: all still refused, except setname_clash
  which still renders the proven-equivalent `seen_set2`.
all other r3 fixtures (b2/b3/b5/b6*/b7*/b9/b11/b13/b15/b17*/b18/b22,
  m_dedup/m_delete/m_drain/m_pop_front/m_remove_*/m_replace/m_resize/
  m_retain/m_swap_remove) -> No fixes available.
```

The envelope did NOT collapse to useless: the plain single-array dedup, the
two-array dedup, the `while`-with-index dedup and the COLL002 hoist all still
render, and the safety spec asserts that explicitly as a non-vacuity check —
six refusals in a row prove nothing on their own.

## Round 4 — retraction: "covered by construction" was true of STATEMENTS only

The round-3 section above says the generic traversal covers new kinds "by
construction" and that "nothing was demoted to warning-only". Both claims
were scoped to the STATEMENT layer, and the text did not say so. At the
EXPRESSION layer the traversal was still an allow-list: `expr_child_exprs`
yields neither child STATEMENTS (a `do:`/`unsafe:` block, a block-bodied
lambda) nor MATCH ARMS, and no `coll_expr_kind_known` existed, so
`EXPR_ASM`/`EXPR_CUSTOM_BLOCK` were silently safe. Five more wrong rewrites:

| fixture | what the expression walk missed | original -> rewritten |
|---|---|---|
| `y1_interp` | `print "{seen.pop()}"` — the hole is inside a plain string literal | `[1,3]` -> `[3]` |
| `y1b_interp_val` | same hole in a `val` initializer | `[1,3]` -> `[3]` |
| `y24_coll002_interp` | same, COLL002 side | `[1,2]` -> `[1,2,2]` |
| `y2_unsafe` | `unsafe:` block body — statements hanging off an expression | `[1,3]` -> `[3]` |
| `y6_match_expr` | `val r = match x: case 2: seen.pop()` — arms of a match EXPRESSION | `[1,3]` -> `[3]` |

Now: `expr_mentions_ident`, `expr_escapes_ident`, `expr_has_unsafe_use`,
`collect_expr_idents`, `collect_expr_binding_names` and `coll_expr_inspectable`
all recurse through `expr_child_exprs` **and** `expr_child_stmts` **and**
`expr_child_arms`; `coll_expr_kind_known` mirrors `coll_stmt_kind_known`, so
an expression kind nothing can enumerate makes the function uninspectable.

**String interpolation is the one thing still not covered by the tree**, and
this record no longer claims otherwise. `"{x}"` parses as `EXPR_STRING_LIT`
with zero children, so the interim rule is textual on purpose: a literal with
a `{` that mentions the tracked name as a bare token counts as a use. It is
over-approximate and cannot be otherwise. The real fix is filed as
`doc/02_requirements/feature/parser_interpolation_holes_as_child_expressions.md`
and benefits every analysis, not this one.

## Round 4 — coverage, and one deliberate tightening

Measured over the tree: **68 real dedup sites in 52 files**; only 5 (7%)
got a Certain fix. Two precision limits, both fixed:

- **Reader results may flow into calls.** `print(seen.len())` passes a FRESH
  value; the old rule refused any argument mentioning the name. ~24 sites.
  `expr_escapes_ident` now treats the result of a proven read-only method as
  not-an-escape, while the array itself still escapes.
- **The Dict moved beside the DECLARATION.** It used to be emitted before the
  loop, which is what made nesting unsafe; emitted after the array's `val`/
  `var` it shares the array's lifetime exactly, so nesting stops mattering.
  ~16 sites. `decl_sibling_before` is replaced by `decl_visible_for`, which
  looks the declaration up among those in scope on the path to the site.
  `nested.spl` and `a1_while_paren` therefore now FIX, verified by execution
  (`[1,2,3,4]` -> `[1,2,3,4]` for both), and their spec examples are flipped
  with that evidence.

One shape got STRICTER, deliberately: `print seen` — the array itself as a
call argument — is now refused where round 3 allowed it. Proving a callee
does not mutate its argument needs interprocedural analysis this does not
have, so it fails closed. `print seen.len()` is fine.

### The real ceiling was an admission rule, not a proof

Those two precision fixes alone moved coverage 5/68 -> 7/68, far short of the
~40 sites they were expected to unlock. The reason was upstream of every
proof: `collection_single_safe_proof` admitted a fix only when the file held
**exactly one** candidate of that code and **no** unsafe one. That rule dates
from when the renderer recovered its edit location by scanning text, where a
second candidate genuinely made the location ambiguous. Proofs now carry the
parser's own `guard_line` / `push_line` / `decl_line`, so the ambiguity it
guarded against no longer exists — it was only suppressing real fixes.

It is replaced by `collection_safe_proofs`, which renders **every** safe site.
Two spec examples flip with A/B-by-execution evidence, both previously
refusing for this reason and this reason only:

- `collection_easy_fix_spec` "more than one `.contains(` line": two DIFFERENT
  arrays searched in one loop. `search_twice([1,4,7,2,5])` is `[1,4,2,5]`
  before and after; both sites now fix.
- `collection_fix_adversarial_spec` a19: the same array NAME as a separate
  local in two functions. `2` / `2` before and after; element types resolve
  per function (`Dict<i64,bool>` and `Dict<text,bool>`).

**One asymmetry this exposed, and it is a real hazard.** For COLL020 two safe
candidates on the same array cannot coexist: the second site's push is a
mutation the first site's proof does not permit, so both are already refused.
For COLL002 they can, because `contains` is a READER — a lookup table read in
two loops proves safe at both, and rendering both emitted
`var known_set: Dict<...>` after the SAME declaration twice. That is a
duplicate binding, i.e. exactly the class of wrong rewrite this record exists
to stop, and it is a common shape in real code. Safe proofs are therefore
deduped by `(receiver, decl_line)`: the first site renders, the rest keep
their warning and get no fix. Covered by
`collection_certain_fix_safety_spec` "two COLL002 reads of one un-mutated
table hoist the Dict once".

**And one mis-attribution in the lint path.** `lint_cli_append_parsed_results`
attached every rendered fix to the FIRST warning of that code and then set a
once-per-file flag, so with two safe sites `simple lint --fix` would have
offered a fix for site B on the diagnostic for site A while `simple fix`
applied both — the round-1 "lint and fix disagree" class, reintroduced one
level down. A diagnostic now carries the fix for its OWN site only:
`collection_render_proven_fixes` takes a `for_line`, and the warning's span
and the proof's `guard_line` are the same node resolved the same way, so the
match is exact.

### Round 3's destructuring rule was implemented stricter than it was written

Round 3 asked for destructuring to **count as a binding**. What landed was
stricter: any binding whose `stmt_get_name` was not a single plain identifier
made the whole FUNCTION uninspectable. That refused a fix for
`dependency_ids` in `native_module_witness_facts.spl` because the function
contains `val (source_content, source_count) = ...` — a pattern that does not
bind `dependency_ids` at all. Sampling the refused sites in the tree, this was
the single largest remaining cause.

`coll_binding_names_of` now reads the names a pattern binds out of the
PARSER's rendering of it (`stmt_get_name`, e.g. the literal `"(seen,k)"`) —
not out of a line of source; that distinction is the whole point of the
round-2 move onto the AST and is not being walked back. Accepted characters
are identifiers, `(`, `)`, `,` and spaces; anything else (`[`, `.`, `*`) is a
form this does not model and still takes the function with it.

The direction is fail-closed by construction: over-counting bindings can only
ADD refusals, because a bound name is a name that may be a different array.
`Some(seen)` yields both `Some` and `seen` and refuses; `(a, b)` yields
neither the receiver and proceeds. Only the inspectability gate is relaxed,
and only for patterns whose every bound name is readable.
`coll_is_plain_identifier` is deleted. Covered by
`collection_certain_fix_safety_spec` c3 (unchanged: rebinding `seen` still
refuses), c3b (binds other names: fixes) and c3c (a `[p, q]` list pattern:
still refuses the function).

### Coverage after round 4, and where the ceiling actually is

Measured with `bin/simple fix --dry-run` from INSIDE the lane worktree over
the 68 real dedup sites in 52 files:

| change | sites fixed |
|---|---|
| round 3 baseline | 5 (7%) |
| reader results may flow into calls; Dict beside the declaration | 7 |
| per-site rendering (the exactly-one admission rule removed) | 8 |
| destructuring binds names instead of blinding the function | **10 (15%)** |

15% is well short of a share worth shipping the Certain door on, and the
reason is no longer in the door. Sampling the refusals:

- **26 of 68 (38%) are never warned about at all.** The detector only matches
  a guard whose value is a bare identifier, so `seen.contains(dep.path)` —
  the most common real shape — produces no COLL002 and no COLL020, and the
  Certain door never sees it. Filed separately as
  `coll020_detector_blind_to_non_identifier_guarded_value_2026-09-19.md`,
  with the two-function CLI reduction that proves it.
- 10 of 68 have a multi-statement guard body, which the detector also rejects.
- The rest are the door working: the array is a parameter, or reassigned
  (`xs = xs.sorted()`), or `.sort()`ed (an in-place reorder is
  membership-preserving and could in principle be allowed, but that is 3
  sites and a new class of reasoning), or the same receiver is deduped in two
  loops (18 sites — one proof permits exactly one push, so two dedup loops on
  one array refuse each other; that is the next real ceiling inside the door).

**Verdict on shipping.** Lint-only is the shippable configuration: the
diagnostics are correct and positioned, and the Certain door refuses rather
than rewriting wrongly. 15% does not clear the bar for turning the fix on by
default, and the honest next step is the detector record above, not further
loosening of the proofs.
