# Bug: `a < b[i]` — bracket index after `<` still misread as generics (reopens a same-day closure)

- **ID:** parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17
- **Severity:** P1 — bootstrap-blocking. The seed cannot parse the compiler's own source.
- **Discovered:** 2026-08-17, while re-baselining an unrelated MIR finding against a fresh seed.
- **Status:** OPEN
- **Reopens:** `parser_array_index_misread_as_generics_2026-06-14.md`, which was marked
  `CLOSED 2026-08-17 — the parser false positive no longer fires`. It still fires.

## Summary

The parser reads `name[...]` as a `[...]`-style generic type application — the exact
defect the 2026-06-14 row describes — when the index expression appears on the
right-hand side of a `<` comparison:

```
--> src/compiler/70.backend/backend/native/regalloc.spl:158:58
158 |   if target_start < block_start_pos[block.block_id]:
    |                                    ^
Use angle brackets: block_start_pos<...> instead of block_start_pos[...]
```

## Why the trigger is `<`, not the indexing

The strongest evidence is inside the failing file itself. Three consecutive lines
index the *same* variable; only the one preceded by `<` fails:

```
156 |  val target_start = block_start_pos[target_id]        # parses fine
157 |  val src_end      = block_end_pos[block.block_id]     # parses fine
158 |  if target_start < block_start_pos[block.block_id]:   # FAILS
```

So the construct `name[expr]` is not itself the problem. On seeing `<`, the parser
commits to a generic-argument parse and then rejects the `[` that follows.

This also matches the closed row's own reproducer, which nobody appears to have
noticed was the same shape:

```
559 |  while j >= 0 and current.selector.specificity < matched[j].selector.specificity:
```

Again an index on the RHS of `<`. The two reproducers are the same defect, which is
why closing one did not fix the other.

## Independent corroboration (not one bad build)

Reproduced at the identical file, line and column by two separately built seeds:

| seed | built | source tree |
|---|---|---|
| `/mnt/data/cgtw2/release/simple` (59,582,624 bytes) | 2026-08-17 11:10Z | clean `wt-vsc-fix`, byte-identical to `origin/main` |
| `/mnt/data/cargo-w0001/release/simple` | 2026-08-17 08:28Z | another lane, independently |

Both built with `cargo build --release --bin simple`, rc read directly (not through a
pipe). A third cross-check (`cargo-target-c2`) ended `exit 143` and is recorded here as
**UNVERIFIED, not corroboration** — earlyoom is actively SIGTERMing `simple` on this host.

## Impact

`regalloc.spl` is compiler source. A seed that cannot parse the compiler's own source
cannot bootstrap it, so this is not a cosmetic lint gap. It is currently masked because
the affected guard fails for this reason *after* the code path most lanes exercise.

## Why the 2026-06-14 closure was premature

That row was closed on source inspection of its single original reproducer
(`src/lib/common/ui/style.spl`). The closure verified that one site, not the defect
class. The `<`-precedes-index shape was never enumerated, so a second live instance in
`src/compiler/**` survived the closure untouched. Two specs are needed here, per the
standing rule: one reproducing `regalloc.spl:158`, and one defect-CLASS spec that walks
`a < b[i]`, `a <= b[i]`, and the `and`-chained form from the style.spl case.

## Not yet done

- No parser fix attempted. Filing only.
- The class spec above is unwritten (the lane assigned to it was killed by a session limit).
- Root cause in the Rust seed parser not localised; note that another lane has
  uncommitted edits under `src/compiler_rust/parser/` (`parser_impl/core.rs`,
  `stmt_parsing/control_flow.rs`, `expressions/postfix.rs`), so whoever picks this up
  should check whether it is already being addressed there before editing.
