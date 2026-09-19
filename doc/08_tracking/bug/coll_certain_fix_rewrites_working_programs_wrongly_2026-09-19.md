# The Certain COLL002/COLL020 auto-fix rewrote working programs into wrong ones

**Status:** FIXED 2026-09-19 on `work/coll-gaps` — the Certain door now proves
safety or refuses.
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

## Fix — a narrow envelope: prove it, or refuse

Four checks, all in `entry_and_fixes.spl`, all fail-closed. Hint-only
(advisory) is an acceptable outcome; wrong code is not.

1. **Dominance** — `collection_decl_dominates_loop`: the declaration must
   precede the hoisted-to loop with NO loop header between them and its block
   still open (no line of smaller indent in between). Rejects (a).
2. **Site containment** (COLL020) — the guard and the push must BOTH lie
   inside that one innermost loop (`loop_line < idx <= block_end`). Nothing
   checked this before.
3. **Whole-function mutation proof** — `collection_function_mutates_outside`
   scans every line of the enclosing function at token boundaries via
   `collection_line_mutates_name` / `collection_rest_is_mutation`, which
   recognise `.<mutating-method>(`, `[i] =`, `=`, `+=`, `-=` at ANY position,
   against a 24-name mutating-method list. Permitted sites: the declaration
   line, and (COLL020 only) the one guarded push the rewrite keeps in step
   with the Dict. A line that both mentions the name and contains `;` is
   refused outright — statement separation on one physical line defeats every
   line-oriented judgement this file makes, so it is not judged. Rejects (b).
   This REPLACES the prefix whitelist as the load-bearing check; the old range
   scans are kept as a cheap pre-filter.
4. **Fresh generated names** — `collection_fresh_identifier` tries
   `{receiver}_set`, then `…_set2`..`…_set10`, against a bare-token scan of
   the WHOLE FILE (stricter than scope, and needs no scope model), and
   returns "" (no fix) when all are taken. Applied to COLL002's `_v` loop
   variable too, which had the same collision hazard. Fixes (c).

## Verification — real CLI

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

Still fixed, and each A/B-checked where it has a driver: `coll020.spl`,
`coll020_two_array.spl`, `coll002_fixable.spl`, `whileidx.spl`
(`while`-with-index, `[1, 2]` before and after).

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

## Not holes (checked, negative results kept)

- `val s2 = seen` — arrays are value-copied at runtime, so assignment
  aliasing is not a mutation channel (probed).
- Closure capture IS by reference, but a fixture proving a WRONG rewrite
  through it did not reproduce. Unproven, not counted — and
  `\y: seen.push(y)` is caught by the token-boundary mutation scan anyway.
- `truncate`/`remove_at`/`delete` do not exist on Array today; they are in the
  mutating-method list regardless, so a future one cannot slip through a list
  nobody re-reads.
- COLL022 has no fix generator at all (`grep -rln COLL022
  src/compiler/90.tools/` is empty), so its known string-interpolation blind
  spot is advisory-only and cannot corrupt code.
