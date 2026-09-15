# Pre-existing test-tree divergence recorded for round 22's landing (2026-09-14)

`.claude/rules/vcs.md` requires that landing on a `check-test-tree-divergence-delta`
PASS also RECORD the pre-existing offender list — an unrecorded step-over is a
violation even when the delta is clean. This file is that record for the
round-22 web↔Chrome parity landing.

## Verdict

```
check-test-tree-divergence-delta: PASS — 3217 pre-existing offender(s),
                                  0 introduced by this range
```

Range: `c56dd5004afb` (origin/main) .. `4003ae8044a0` (this change), run in the
foreground under `timeout 900`, exit code captured into a variable on the line
after the invocation (never through a pipe). rc=0.

## The offender list

Saved by the helper to
`$TMPDIR/test_tree_divergence_preexisting.txt`, which is machine-local and not
durable, so its identity is pinned here instead:

| | |
|---|---|
| lines | **3945** |
| sha256 | `1f4245e3e0ff379e047d7f34d93eadd8cb537499092071e565368a3c478dd55a` |
| first entry | `integration:app/add_remove_log_modes_spec.spl` |

Largest clusters:

| count | prefix |
|---|---|
| 432 | `unit:std/improved` |
| 317 | `unit:lib/common` |
| 200 | `unit:std/deep` |
| 172 | `unit:compiler/deep` |
| 141 | `unit:lib/nogc_async_mut` |
| 100 | `unit:compiler/complete` |

None of these is owned by, touched by, or related to this change. The verdict
line's 3217 is the offender COUNT the delta helper compares; the 3945 lines are
the saved list's entries.

## Mirror pairs this range touches

Enumerated rather than asserted from memory, per the 2026-09-12 note in
`.claude/rules/vcs.md`:

```
git diff --name-only c56dd5004afb..4003ae8044a0 \
    -- test/01_unit test/unit test/02_integration test/integration
```

```
test/01_unit/browser_engine/absolute_auto_width_shrink_to_fit_spec.spl
test/01_unit/compiler/hir/materialized_payload_closure_reentrancy_breaker_spec.spl
```

The first is this round's new spec; it has no twin under `test/unit/`, so it
adds no pair. The second is not this change's file — it arrived on `origin/main`
inside the range base. The delta helper's own offender-list diff, not this
enumeration, is the authority, and it reports **0 introduced**.

## Related

`doc/10_metrics/ui/web_chrome_parity_round22_2026-09-14.md`.
