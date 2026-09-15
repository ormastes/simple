# macOS Stage 2 sanity: module surface registry graph promotion fails after phase 2 (2026-09-13)

Status: **CLOSED (2026-09-13) — not fixed here, and not by the change this
record was opened for.** The blocker was already gone from `main` by the time it
was diagnosed: `460aa9781cc` ("fix(hir): stop failing surface promotion on a
repeat-promote post-condition", the Linux BOOT-7 fix filed as
`stage2_module_surface_registry_graph_promotion_failed_2026-09-13.md`) landed on
`main` at 08:12 via PR #754, **after** run 19's PR #753 merged at 07:58. Run 19
therefore measured a tree that did not carry it, and this record described a
defect that a sibling lane had already fixed.

**Measured, not inferred.** Run 20's Stage 2 `native-build` was replayed verbatim
from its own `stage2-command.transcript` against `origin/main` @ `601bc2787b2`
with the diagnostic rewrite REVERTED (886 compiled, 0 failed, 450s). The
resulting candidate runs the positional Stage-3 route with
`grep -c 'promotion failed'` = **0** and logs
`phase2:surface:file:promote-done` / `commit-done` / `released seq=2`. So the
promotion succeeds on this lane without any change of ours: the 24-operand
`not rt_transient_heap_promote(a) or not ...(b) or ...` chain was **not** the
false, and an earlier draft of this record that said it was has been withdrawn
rather than left standing.

What this lane contributes is therefore narrower and is stated as such: a
fail-closed diagnostic so the next occurrence names itself (below), the
correction that the rejected candidate IS preserved (below), and the finding
that macOS has converged with Linux on site 8.

Successor blocker on macOS: the Stage-3 route now SEGVs five phases later, in
`native_compile` / `serialize_mir_function` — site 8,
`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`.

## Provenance — this is a successor, not a regression

It was uncovered by fixing
`stage2_sanity_darwin_link_passes_lc_2026-09-13.md` (the darwin link line passed
`-lc`, which macOS does not ship, and then could not resolve libSystem because
the resolved Xcode clang had no SDK). With both cleared, the sanity hello world
COMPILES AND LINKS for the first time on this lane, and the gate advances past
the frontend smoke to the struct-receiver/runtime-capability check — where it
now fails for a stated, different reason.

Do not reopen the link records for this. The link is no longer involved: the
failing step is a `native-build` that gets as far as phase 2 and then cannot
promote its module surface registry graph.

## Verdict, verbatim (run 19)

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
stage: stage2
  diagnosis: the PRIMARY log carries no diagnostic text, but a sibling log
             written by another sub-step of this stage does. The stage did
             not fail where the primary log was produced.
  real log:  <evidence-root>/stage3/aarch64-apple-darwin/stage2-receiver.log
  2 diagnostic line(s) found there. First 5:
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
    | error: in-process native-build: Module surface registry graph promotion failed after phase 2
exit:  3
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stage 1 admitted. Stage 2 built its full closure clean (886 compiled, 0 cached,
0 failed) and was rejected solely by this.

## Correction: the candidate WAS preserved — it is in a different directory

This record's original "no rejected Stage 2 candidate is preserved" was a
look-in-the-wrong-place error, and no script change was needed. The exit-3 arm
already keeps it: `bootstrap-from-scratch.sh:3091-3111` `mv`s the candidate to
`<evidence-root>/stage2-rejected/<PLATFORM>/simple` and writes a
`rejection.env` beside it (`reason=stage2-struct-receiver-failed`, with the
sha256 and both evidence paths). `stage2/<PLATFORM>/` is empty precisely
*because* the binary was moved out of it. Run 20 confirms:
`bootstrap-run20/stage2-rejected/aarch64-apple-darwin/simple`, 139,327,000 B,
sha256 `630ad64b7194eec6873fdcd6382c83ecad4b23f760d303a57eac5b26f214e0ed`.
Note it lands `chmod 400` — copy it out and `chmod +x` before a witness run.

## Run 20 evidence

Same command and a virgin evidence root, on a tree that carries both
`460aa9781cc` (via `main`) and the diagnostic rewrite.
`grep -c 'promotion failed' stage2-receiver.log` = **0**. The route advances
through `parse`, `hir`, `monomorphize`, `mir` and `native_cache` and dies in
`native_compile`:

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 139)
```

macOS crash report `simple-2026-09-13-083808.ips`, triggered thread frame 0:
`compiler__mir__mir_json__serialize_mir_function`. That is site 8 verbatim, so
this lane's blocker is now the same one Linux BOOT-7 reached after
`460aa9781cc` — the two lanes have converged. The counterfactual replay above
reaches phase 2 equally cleanly, which is what establishes that `460aa9781cc`,
not the rewrite, is what moved this lane.

## Why the diagnostic stays even though it fixed nothing

`module_surfaces_promote` had 26 routes to a bare `false` and the driver's
message named none of them, so the only way to learn which fired was another
~25-minute cycle. `module_surfaces_promote_reason` now returns "" or a text
naming the field, the surface index and its logical/canonical/package names,
the registry cardinalities, and a **scope sentinel** — a promote of a freshly
built carrier, which separates "the transient array scope is not active+paused,
so the runtime answers false for EVERY value" (`runtime_native.c:2430`) from a
genuinely unpromotable field. The 24-operand boolean chain is gone too — not
because it was measured to misbehave (it was not), but because a chain that can
only answer an unnamed false is untriageable, and this file's immediate
neighbours already carry comments about this backend mis-lowering long boolean
and receiver forms. That is a readability/diagnosability argument, and it is the
only one claimed for it. The driver interpolates the reason. Spec:
`test/01_unit/compiler/hir/module_surface_promote_reason_spec.spl`, 4 examples /
0 failures.

## Where to look

The message comes from the in-process native-build's module-surface/registry
layer, not the linker and not the frontend. `stage2-receiver.log` is the real
log; the primary `stage2-native-build.log` is silent, as the bootstrap's own
diagnosis line says.

## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 \
   --full-bootstrap --mode=dynload --jobs=half
```

from a worktree with a VIRGIN evidence root (the tree is written read-only —
`chmod -R u+w` before `rm -rf`, and remove
`.simple/storage/build/.simple-bootstrap-locks` if a previous run was killed, or
the next run dies with `timed out waiting for bootstrap output ownership`).

**Trap that cost one full cycle:** do not wrap a wait-for-completion loop in a
`timeout`, and do not let a background waiter be killed. Both signal the
bootstrap's process GROUP, and the run dies with a bare `Terminated: 15` that
looks like a build failure. Poll with short, unbounded foreground checks.

## Related

- `doc/08_tracking/bug/stage2_sanity_darwin_link_passes_lc_2026-09-13.md`
  (predecessor, RESOLVED — PRs #752, #753)
- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
  (predecessor's predecessor, RESOLVED)
- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md` (runs 1-19)
