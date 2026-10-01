# check-guard-wiring counts `#`-comment mentions as wiring edges

Status: OPEN (finding recorded, fix deliberately NOT applied — see blast radius)
Filed: 2026-08-31

## Defect

`scan_wiring()` in `scripts/check/check-guard-wiring.shs` builds its
referrer -> guard edges from a **broad textual** match: any mention of a guard's
basename in `scripts/`, `.github/`, `src/`, `bin/`, `tools/`, `config/` counts as
an invocation. That over-approximation is deliberate and documented (a narrow
call-syntax model would miss the `var="$repo_root/scripts/check/x.shs"` form the
pre-push hook uses).

It already carries one prose exception: lines shaped like
`*_note=` / `*_report=` / `*_report_note="..."`, because those are operator
help-text, not invocations.

There is a **second prose shape it does not exclude: a whole-line `#` comment.**

Concrete instances found on `origin/main` @ `b0be388ec46`:

- `scripts/check/check-c-runtime-compiles-push.shs:181-182` names
  `build-core-c-bootstrap-runtime-capsule.shs` and
  `scripts/audit/cocoa-sffi-contract.shs` inside a `#` block describing what that
  guard does *not* cover.
- `scripts/check/check-no-unresolved-runtime-symbols.shs:305` does the same for
  the core-C capsule.

Both named scripts are genuinely unrunnable in CI — one needs QEMU/an FPGA/a
board, the other is macOS-only — and were correctly recorded as debt (one
baselined, one opted out with a reason). The phantom edges made the ratchet
report both as **"stale, now wired"**, i.e. it demanded the deletion of two
*true* lines. Deleting them asserts in writing that two unrunnable guards are
gates.

## Why the obvious fix was not applied here

Adding `$GREP -v -E '^[[:space:]]*#'` to the same filter chain is one line and is
principled (a `#` line cannot hold an executed invocation in a shell script or a
workflow `run:` block). It was implemented and measured on this tree, then
reverted, because the blast radius is a separate program:

```
check-guard-wiring: FAIL — 1497 guard(s) checked, 15 NEW unwired ...
```

**15 guards lose their only edge**, i.e. they are reached today *solely* through
comment prose and are in truth wired to nothing:

    check-aspect-seal.shs                     check-post-bootstrap-stage4-sspec.shs
    check-bootstrap-must-pass.shs             check-seed-builds-push.shs
    check-bootstrap-stage2-struct-receiver.shs check-seed-extern-registry.shs
    check-bootstrap-stage3-selfverify.shs     check-test-tree-divergence.shs
    check-cosmos-ftl-policy.shs               check-untyped-return-value.shs
    check-critical-release-seal.shs           lint-cached.shs
    check-f64-call-abi.shs                    check-no-revert-push.shs
    check-native-option-bool-llvm-verify.shs

That set is load-bearing: `check-seed-builds-push.shs`,
`check-test-tree-divergence.shs` and `check-no-revert-push.shs` are documented in
`.claude/rules/vcs.md` as **mandatory pre-push guards**. If they are reachable
only via comment text, either the pre-push hook chain no longer names them
executably or the hook root set is incomplete — a real gap that is strictly
larger than a filter tweak and must not be discovered as a surprise CI red in an
unrelated lane.

## Interim action taken (2026-08-31)

The two stale lines were removed, which is what the ratchet prescribes and what
its own model makes true:

- `scripts/check/guard_wiring_unwired_baseline.txt`: dropped `cocoa-sffi-contract.shs`
- `scripts/check/guard_wiring_optout.txt`: dropped `build-core-c-bootstrap-runtime-capsule.shs`

This is fragile in a stated, bounded way: if either `#` comment is ever edited
away, both scripts reappear as NEW unwired and the ratchet will demand a decision
again — which is the correct behaviour, not a regression.

## Owner / next step

Whoever takes the 15-guard set above: apply the comment filter, then for each
guard decide wired-vs-opt-out on evidence. Verify the pre-push chain names its
mandatory guards executably rather than only in prose.
