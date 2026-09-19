# The Certain COLL002/COLL020 auto-fix rewrote working programs into wrong ones

**Status:** SUPERSEDED 2026-09-19 by
coll_certain_fix_textual_proofs_disagree_with_parser_2026-09-19.md. The
symptoms below are accurate and were executed; the FIX section is a
retraction, because the code it described is deleted. Originally: "the
Certain door now proves safety or refuses."
**Severity:** Blocking — a `Certain`-confidence machine-applied rewrite
silently changed program output. `simple fix <file>` needs no flag and writes
in place.
**Pre-existing, not only a regression.** Classes (a) and (c) below were
offered by `simple fix --dry-run` at the base commit `7c875a81067` as well, so
this is a defect in the **shipped** auto-fix. That code is on
`work/rc1-dataframe-sosix` and **must not land as-is**. Class (b) was
lint-silent at base and is newly exposed to lint by the widened COLL020
detector (`doc/08_tracking/bug/
coll020_lint_fix_disagree_two_array_dedup_2026-09-19.md`), so its lint-side
exposure belongs to that lane.
**Affected file:** `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`
(`collection_002_fix`, `collection_020_fix`)
**Spec file:** `test/01_unit/compiler/lint/collection_certain_fix_safety_spec.spl`,
mirrored byte-identically at `test/unit/compiler/lint/`
**Path:** `bug` track. Found by a Fable review that ran the original AND the
rewritten program for each fixture instead of reading the diff.

## Symptom — three classes, each verified by execution

| fixture | original | after `simple fix` |
|---|---|---|
| `nested.spl` | `[1, 2, 3, 4]` | `[1, 2, 2, 3, 1, 3, 4]` |
| `outer_mut.spl` | `[1, 2, 9, 9]` | `[1, 2, 9, 2, 9, 9]` |
| `pop_expr.spl` | `[1, 2, 3, 3]` | `[1, 2, 3]` |
| `coll002_pop.spl` | `[3, 1]` | `[3, 3, 3, 1]` |
| `setname_clash.spl` | `1` | `2` |

**(a) The Dict was hoisted in front of the INNERMOST loop.**
`collection_enclosing_loop_line` returns the nearest enclosing loop of the
guard, and the Dict declaration was inserted there. When the tracking array
is declared outside an *enclosing* loop, the Dict is re-created on every
outer iteration while the array is not, so membership resets:

```
var seen: [i64] = []
for g in groups:
    for x in g:                  # <- Dict was declared here
        if not seen.contains(x):
            seen.push(x)
```

The only precondition was `decl.1 >= loop_line` — the declaration merely had
to come BEFORE the loop, which it does.

**(b) `collection_is_mutation_of` is a line-PREFIX whitelist.** It matched
only `"{name} = "`, `"{name}.push("` and friends at the START of a trimmed
line, so `val dropped = seen.pop()` and `val used = allowed.pop()` were
invisible, and the Dict kept entries the array no longer had.

**(c) `{receiver}_set` was emitted unconditionally**, shadowing a user
binding of the same name.

## Fix — SUPERSEDED, see the record below

**Everything this section used to describe has been replaced and its code
deleted.** It claimed four textual checks — `collection_decl_dominates_loop`,
`collection_function_mutates_outside`, `collection_line_mutates_name`,
`collection_fresh_identifier` and their helpers — in the present tense. None
of those functions exists in `src/` any more (0 definitions), and describing
deleted code as current is how a record stops being evidence.

The approach was right in intent and wrong in kind: it answered questions
about statement extent, block extent, argument position and binding by
reading source TEXT, and a later review broke all four of those checks seven
more ways, then four more after that. The proofs now live on the AST, in
`collection_fix_proofs` (`collection_patterns.spl`), and
`entry_and_fixes.spl` only renders the edit at sites the AST proved. The
Dict is emitted beside the ARRAY DECLARATION rather than before the loop, so
the nesting hazard class (a) describes is removed rather than detected.

**Read instead:**
`doc/08_tracking/bug/coll_certain_fix_textual_proofs_disagree_with_parser_2026-09-19.md`,
which supersedes this section and carries rounds 2, 3 and 4.

This record is retained for its SYMPTOM table above — the five executed
before/after outputs, and the fact that classes (a) and (c) were offered at
the lane base `7c875a81067` and are therefore a defect in the shipped
auto-fix, not only a regression. That part remains true and is the reason
`work/rc1-dataframe-sosix` must not land the old generator as-is.

## Verification — real CLI (as of round 1; superseded, see the record above)

```
$ bin/simple fix fx/nested.spl        --dry-run  ->  No fixes available
$ bin/simple fix fx/outer_mut.spl     --dry-run  ->  No fixes available
$ bin/simple fix fx/pop_expr.spl      --dry-run  ->  No fixes available
$ bin/simple fix fx/coll002_pop.spl   --dry-run  ->  No fixes available
$ bin/simple fix fx/setname_clash.spl --dry-run
  [COLL020] track membership in `seen_set2` Dict instead of `.contains` on `seen`
```

`setname_clash` is fixed rather than refused because the fresh name makes the
rewrite provably equivalent, and that was checked by execution, not argued:
original prints `1`, rewritten prints `1`, and the user's `seen_set`,
`seen_set[99] = true` and `seen_set.len()` are untouched.

Still fixed, and every one A/B-checked by execution with a driver added:
`coll020` `[3,1,2]` -> `[3,1,2]`, `coll020_two_array` `[3,1,2]` -> `[3,1,2]`,
`coll002_fixable` `[1,5,2]` -> `[1,5,2]`, `whileidx` (`while`-with-index)
`[1,2]` -> `[1,2]`.

## One spec expectation narrowed, deliberately

`collection_fix_adversarial_spec`'s **a16** asserted a Certain COLL002 fix for
a nested loop with `allow.push(2)` in the outer body, on the argument that the
hoisted population pass re-runs per outer iteration and therefore re-reads the
mutated array. That argument is probably true. It is also the same
reasoning-about-re-population-frequency that produced the wrong rewrites
above — `outer_mut.spl` is the COLL020 analogue of exactly that shape. Under
"prove it or refuse" a16 fails two proofs (non-dominating declaration, and
mutation elsewhere in the function), so it is now hint-only. The example and
its docstring record the flip and why.

## Not holes (round-1 findings; the first two are still true, the third was wrong)

- `val s2 = seen` — arrays are value-copied at runtime, so assignment
  aliasing is not a mutation channel (probed).
- Closure capture IS by reference, but a fixture proving a WRONG rewrite
  through it did not reproduce. Unproven, not counted. A mention inside a
  lambda is treated as unsafe regardless.
- CORRECTION, round 3: this bullet used to say `truncate`/`remove_at`/
  `delete` were in a mutating-method list so a future mutator could not slip
  through. It did the opposite — `fill`, a real runtime mutator, was absent
  from that list and read as a harmless call, turning [1,2,1,2] into [1,2].
  The list is now an allow-list of proven READERS and the default is unsafe.
- COLL022 has no fix generator at all (`grep -rln COLL022
  src/compiler/90.tools/` is empty), so its known string-interpolation blind
  spot is advisory-only and cannot corrupt code. The parser-side fix is filed
  as doc/02_requirements/feature/
  parser_interpolation_holes_as_child_expressions.md.
