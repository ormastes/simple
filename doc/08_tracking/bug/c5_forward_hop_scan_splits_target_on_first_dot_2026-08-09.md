# C5 `forward_hop_scan` splits a forwarding target on the FIRST dot — wrong receiver projection and a target method that does not exist

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  filed OPEN while landing C2 typed forwarding, which could not fix it here:
  `src/compiler/90.tools/verify/forward_hop_scan.spl` is C5 territory and was
  explicitly off-limits to this session.
- **Found:** 2026-08-09, executing lane C2 of
  `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §3.
- **Area:** compiler forwarding — C5 hop axis
- **Severity:** wrong measurement. The hop count C5 reports for any
  multi-segment forwarding path is computed from a target method name that is
  not the method being called.

## The disagreement

`src/app/desugar/forwarding.spl` is the authoritative forwarding mechanism.
For a Phase 2 alias it splits the target on the **last** dot
(`forwarding.spl:381`, `find_last_char(right, ".")`): everything before is the
receiver projection, the final segment is the method.

`src/compiler/90.tools/verify/forward_hop_scan.spl:parse_forward_decl` splits
on the **first** dot instead (`:112`, `_split_once(target, ".")`), then runs
`_ident_prefix` over each half — which additionally truncates whatever remains
at the next dot.

For a single-segment path (`inner.len`) the two agree, which is why every
existing fixture passes. They diverge as soon as the path has more than one
segment.

## Executed evidence

Probe run under `SIMPLE_MODULE_LIMIT=4000 bin/simple run`, input line
`    alias fn push = inner.items.push`:

```
=== desugar text generator (authoritative) ===
class C:
    fn push():
        self.inner.items.push()

=== C5 forward_hop_scan ===
count=1
field=inner method=items
```

The generator forwards through `inner.items` and calls `push`. C5 reports the
receiver field as `inner` and the target method as `items` — `items` is an
intermediate field, not a method, and the actual call target `push` is dropped
entirely.

## Why it matters beyond the parse

`_walk_chain` (`forward_hop_scan.spl`) follows a chain by looking the reported
`target_method` up as the next declaration's `logical_name`. Fed `items`
instead of `push`, the walk searches for the wrong name: it terminates early
(under-counting hops) or matches an unrelated declaration that happens to be
named `items`. Either way the `ZFP_AXIS_HOPS` number is not a measurement of
the path the generator actually produces.

`alias fn NAME = FIELD.SUB.METHOD` is a documented, supported form —
`forwarding.spl:325` states "FIELD.METHOD can be a dotted path like
inner.items.push" — so this is not an unsupported input.

## Unblock condition / fix

In `parse_forward_decl` (`src/compiler/90.tools/verify/forward_hop_scan.spl:105-120`),
split `target` on the LAST dot rather than the first, and do not run
`_ident_prefix` over the receiver half (a projection is legitimately dotted;
only the method segment is a bare identifier). The C2 lowering already
implements exactly this and is pinned by a spec:
`src/compiler/20.hir/hir_forward_lowering.spl:_parse_alias_line` and the
"receiver projection uses the LAST dot" group in
`test/01_unit/compiler/hir/hir_forward_lowering_spec.spl`.

Reproduce:

```bash
SIMPLE_MODULE_LIMIT=4000 bin/simple test test/01_unit/compiler/hir/hir_forward_lowering_spec.spl
```

The "receiver projection uses the LAST dot (C5 scanner divergence tripwire)"
group is the regression tripwire; it goes red if the C2 side is ever changed to
match C5's current (wrong) behavior.

## FIXED 2026-08-09

`parse_forward_decl` now splits the target on the LAST dot, matching the
generator. Two helpers were added to `forward_hop_scan.spl`: `_rsplit_once`
(last-occurrence split) and `_dotted_ident_prefix` (leading dotted identifier
path, so the receiver half is no longer truncated at a dot by the
single-identifier `_ident_prefix`).

`receiver_field` is now a dotted PATH rather than a single identifier. Audited
consumers: `receiver_field` is read only inside `forward_hop_scan.spl` itself
(`_walk_chain`, which re-joins it into `to_symbol`). `zero_forward_path_gate.spl`
consumes `ForwardEdge` only via `to_symbol` (message text) and `edges.len()`
(the hop count), so no consumer assumed a single identifier and no
representation is left half-migrated.

Executed evidence, input `alias fn push = inner.items.push`:

| | before | after |
|---|---|---|
| `receiver_field` | `inner` | `inner.items` |
| `target_method` | `items` | `push` |

And for `a.b.c.d`: `field=a method=b` before, `field=a.b.c method=d` after.
A dotless target (`alias fn bare = push`) is reported as no declaration both
before and after, matching the generator's `empty_result`.

Hop-axis change on a two-link chain (`alias fn draw = inner.gfx.render` +
`alias fn render = backend.flush`), measured through
`check_all_zero_forward_paths`:

| | before | after |
|---|---|---|
| `edges.len()` (ZFP_AXIS_HOPS) | 1 | 2 |
| gate violations | 4 | 5 |

The under-count was the predicted `_walk_chain` failure: fed `gfx` (an
intermediate field) instead of `render`, the walk found no declaration by that
name and stopped one hop early. The gate verdict stays `ok=false blocked=true`
either way (the three MIR axes remain unmeasured), so the defect never showed
up as a verdict flip — only as a wrong number inside a blocked verdict.

No hop count changes on the real tree today: `src/` currently contains ZERO
multi-segment alias targets, which is why the defect was latent. This fix is
correctness-ahead-of-use for the form `forwarding.spl:325` documents as
supported.

Pinned by `test/01_unit/compiler/tools/verify/forward_hop_scan_spec.spl`, which
asserts `receiver_field` and `target_method` as SEPARATE fields. A
text-reconstruction oracle cannot pin this: `field + "." + method` re-joins to
the same string under either split point, so a round-trip check is a tautology
here and passes under the bug. Sabotage-verified by reverting to the first-dot
split: 6/6 pass fixed, 2/6 pass sabotaged (only the single-segment control and
the dotless case, exactly the two cases where the parsers agree), 6/6 pass
restored.
