# macOS Stage 2 sanity: module surface registry graph promotion fails after phase 2 (2026-09-13)

Status: OPEN. This is the CURRENT macOS Stage 2 blocker, newly exposed by run 19.

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

## No artifact to hand forward

Unlike runs 17 and 18, **no rejected Stage 2 candidate is preserved** — the
exit-3 path leaves `<evidence-root>/stage2/aarch64-apple-darwin/` empty. The
~40-second witness loop that made the link defects tractable (rebuild a
three-line hello world with the rejected candidate) is therefore NOT available
here; whoever picks this up either reruns the ~25-minute Stage 2 or arranges for
the candidate to be preserved on this exit path first. Making the exit-3 path
preserve its candidate the way the sanity-FAIL path does is probably the single
highest-leverage first step.

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
