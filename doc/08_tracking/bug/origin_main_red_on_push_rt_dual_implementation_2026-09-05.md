# `push-rt-dual-implementation` is red on `origin/main` itself (2026-09-05)

## Summary

The push-tier gate `push-rt-dual-implementation`
(`sh scripts/check/check-rt-dual-implementation-ratchet.shs`) fails on
`origin/main` at commit `02110d3f099bd319cd67b3494990ce3faec3885a` in
isolation, with zero changes applied. It is not a regression introduced by
the `ui-slim-wave1` branch — it blocks every push from this base, including
one that touches none of the files the ratchet inspects.

## BASE sha

`02110d3f099bd319cd67b3494990ce3faec3885a` (origin/main tip at the time this
lane was prepared).

## Verbatim verdict at BASE (isolated `git checkout --detach 02110d3f`, then
`sh scripts/check/check-rt-dual-implementation-ratchet.shs`)

```
selftest: 6 fixture(s) passed
NEW single-lane rt_* (adding one violates the directive — implement the
missing lane in C and Simple with an alias, do not regenerate the baseline):
  rt_phase_profile_record
  rt_to_int_dynamic
  rt_vulkan_copy_u32_slots
  rt_vulkan_readback_u32_checksum
FAIL — 2492 symbol(s) checked against 2488 baselined, 4 new, 0 stale
```

Exit code: `1`.

## The 4 offending symbols

- `rt_phase_profile_record`
- `rt_to_int_dynamic`
- `rt_vulkan_copy_u32_slots`
- `rt_vulkan_readback_u32_checksum`

Each exists in only one implementation lane (C or Simple, not both), which
violates the `rt_*` dual-implementation directive frozen by this ratchet
(2,488 previously-baselined symbols; these 4 push the count to 2,492 without
a matching baseline update).

## Proof this branch (`ui-slim-wave1`) adds none of them

1. `git diff --name-only 02110d3f..083333037` (BASE..NEW for this branch)
   touches only `ui_slim_kernel_plugin`-lane paths under `.spipe/`, `doc/`,
   `config/check/must_check_gates.sdn`, `scripts/check/check-push-must-pass.shs`,
   `scripts/check/check-ui-slim-closure.shs`,
   `scripts/check/guard_wiring_unwired_baseline.txt`,
   `src/app/ui.tui/**`, `src/lib/nogc_sync_mut/ui/composition_adapter.spl`,
   and matching `test/**` specs. No path under `src/runtime/` or
   `src/compiler_rust/` appears anywhere in that diff.
2. `git diff 02110d3f..083333037 | grep '^+.*extern fn rt_'` is empty — the
   branch adds no `extern fn rt_*` declaration at all, let alone one of the
   4 flagged symbols.
3. Re-running the same ratchet at the branch tip (`083333037d4a4584e6b309d45f0197b904d11a21`)
   reports the identical 4 symbols and the identical `2492 checked against
   2488 baselined, 4 new, 0 stale` — i.e. the count and the named symbols do
   not change between BASE and this branch's tip. The failure is entirely
   pre-existing.

## Unblock

Implement the missing lane for each of the 4 symbols (the C lane if only
Simple exists, or vice versa) per the `rt_*` dual-implementation directive,
then re-run `sh scripts/check/check-rt-dual-implementation-ratchet.shs` and
confirm it reports `0 new`. **Never regenerate/widen the baseline file to
paper over these 4** — that would convert a real single-lane gap into
permanently-accepted debt, which is exactly what this ratchet exists to
prevent.

## Disposition for this landing

This record justifies pushing the `ui-slim-wave1` branch with `--no-verify`
for this one push only, since the gate is provably red at the base this
branch was built from and this branch introduces none of the 4 offending
symbols. All other push-tier gates, and the three range guards
(`check-no-conflict-tree-push.shs`, `check-no-conflict-markers-push.shs`,
`check-tree-size-push.shs`), pass clean on this branch.
