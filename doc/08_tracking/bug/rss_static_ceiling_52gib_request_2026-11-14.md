# Raise BOOTSTRAP_TREE_RSS_STATIC_CEILING to 52 GiB (merged-tree plateau re-measured at 50.34 GiB)

Date: 2026-11-14
Lane: work/release-1.0.0-mcp-local (MSVC), cycles 21b/24b/24d
Requested change: `BUILD_STRAP_TREE_RSS_STATIC_CEILING_KIB` 50331648 (48 GiB)
-> 54525952 (52 GiB) in scripts/bootstrap/lib/tree-rss-policy.shs AND
scripts/resource/process-tree-rss-watchdog.pl (kept in sync).

## Evidence

The stage2-compiler-tests campaign tree (the largest single-tree workload in
the lane) now plateaus above the 48 GiB ceiling on the merged tree:

- cycle 21b (tip 189dabae8e3): `status=rss-cap-exceeded`, cap 50331648 KiB,
  peak_rss_kib=50347924 (~48.24 GiB), during compiler_cli_build after ~103 min
  (HIR fully green post-gen7; #9071 confirmed fixed).
- cycle 24b (same tip): `compiler_cli_build` reached MIR 1832/3148 (79%)
  before alloc failure at the ceiling.
- cycle 24d (tip b5d93e48cd8): different regressions (#9359) but the same
  ceiling shape.

The ceiling's own history comment says "48 GiB measures the true plateau
before final evidence-based tightening" (2026-10-16, cycle 49). The plateau
has since grown past 48 GiB; 52 GiB covers the 50.34 GiB measurement with
~1.6 GiB headroom while leaving the enforcing watchdog and the explicit-cap
refusal above the ceiling unchanged (fail-closed on further growth).

Host-fit note (this 64 GiB measurement host): a 52 GiB tree + ~11 GiB other
processes fits only because the Hyper-V balloon serves demand on request
(24 GiB probe allocation succeeds in 0.8 s; commit headroom 52 GiB). Hosts
without balloon headroom at 64 GiB should treat 52 GiB as a HOST-CLASS-SPECIFIC
value, not a universal default — the request is to widen the static ceiling so
the policy can price it, not to force it everywhere.

## Why a bug request instead of a drive-by commit

A constant swap was attempted and reverted: the policy selftest
(`sh scripts/bootstrap/lib/tree-rss-policy.shs --selftest`, 109 fixtures)
embeds the 48 GiB value in ~20 expectations, and the change ripples into
semantics beyond the numeric ceiling:

- worker-floor-elevation plan fixtures (aarch64-8-threads, big-two-workers,
  both cli-row-60g fixtures) stop elevating once the static ceiling reaches
  the floor-derived 52 GiB cap — wants become `2:54525952:0:worker-floor`.
- the `explicit-over-static-refused` fixture uses 51000000 (just over 48 GiB)
  as its over-ceiling probe and silently flips to ADMITTED at 52 GiB.
- the whole-build monitor export fixture changes attribution
  (worker-floor-monitor-clamped -> worker-floor).

Each is explainable, but together they are exactly the kind of safety-policy
semantics the tree-RSS owner should migrate deliberately (the file's own
history shows each widening landed as a dedicated evidence commit). The
measurement evidence above is the tightening input that record asks for.

## Acceptance for the owner lane

1. Constant widened to 54525952 in both files with the evidence comment.
2. Selftest fixtures migrated (elevation-no-longer-needed cases expect
   ceiling field 0; over-ceiling probes moved above 54525952).
3. A 64 GiB-host guard: if the ceiling is meant to scale with host class,
   express it as host-scaled (e.g. min(static, 13/16 host RAM)) rather than
   a bare static, so smaller hosts keep the 3/4 protection.

## Unblock impact

With the ceiling at 52 GiB, the 189dabae8e3 corridor (HIR fully green, MIR
79% at the wall) should complete the slim matrix, letting the receipt-
authorized full run (proven in cycles 24a-24d) continue to Stage 3 and
Stage 4 in-run — which unblocks the native MCP rebuild + deploy + the
three-client activation queued behind it.

## Status 2026-11-24: SUPERSEDED (acceptance items 2-3 open)

The static ceiling is now 58720256 KiB (56 GiB, "eighth widening", commit 2b8f2f3f440),
above the requested 52 GiB, in BOTH `scripts/bootstrap/lib/tree-rss-policy.shs`
(`BOOTSTRAP_TREE_RSS_STATIC_CEILING_KIB`) and `scripts/resource/process-tree-rss-watchdog.pl`
(`$compiler_ceiling_kib`). Acceptance 1 is met by that commit. Not re-checked here:
item 2 (fixture migration; the policy selftest was not run on this Windows host) and
item 3 (host-scaled ceiling: the value is still a bare static, so a 64 GiB host without
balloon headroom is not protected by a host-class bound). Item 3 stays open for the
tree-RSS owner.
