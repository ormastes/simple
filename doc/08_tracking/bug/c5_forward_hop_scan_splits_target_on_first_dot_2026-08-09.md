# C5 `forward_hop_scan` splits a forwarding target on the FIRST dot — wrong receiver projection and a target method that does not exist

- **Status:** OPEN — found while landing C2 typed forwarding. Not fixed here:
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
