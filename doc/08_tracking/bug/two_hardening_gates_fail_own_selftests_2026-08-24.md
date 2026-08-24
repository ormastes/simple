# Two hardening gates fail their own selftests once the file_read overflow is gone

**Date:** 2026-08-24
**Severity:** MEDIUM (two Phase 5 / Phase 8 exit gates report `ERROR — nothing was checked`, so neither can produce evidence)
**Status:** OPEN — recorded, not fixed (investigation capped at three cycles)
**Related:** `seed_file_read_infinite_recursion_stack_overflow_2026-08-23.md` (fixed in `1ca19a1e31a`) was masking these — every gate crashed before reaching its own logic, so all three read as the same failure.

## Measured at the clean tip

Run in a fresh `git worktree` at `da8ecf15b570` (NOT the shared working copy,
which is missing hundreds of origin files and cannot be trusted for this):

| gate | verdict |
|---|---|
| `check-aspect-seal.shs` | `PASS — 1 aspect(s) checked, unbound-required=0 late-activation=0 post-weave-recheck=ran` |
| `check-completeness-seal.shs` | `ERROR — nothing was checked (selftest failed: positive-fixture-not-admitted positive-fixture-not-published open-dyn-in-critical-not-detected id-collision-not-detected)` |
| `check-critical-package-pins.shs` | `ERROR — nothing was checked (selftest failed: waiver-no-owner-not-detected waiver-no-expiry-not-detected waiver-expired-not-detected)` |

Neither gate script nor its census has been touched since 2026-08-21
(`72ddebf2094`, `2db75e0d35a`), so no owning lane is mid-fix on them.

## What is established about the package-pins failure

Exactly the three `waiver_*` negatives fail; the positive fixture and the other
three negatives pass. The waiver block is never parsed at all:

```console
$ bin/simple run src/app/check/critical_package_pins_census.spl \
    --checks test/fixtures/package_pins/checks_clean.sdn --today 2026-08-21 \
    --package test/fixtures/package_pins/base/simple.sdn \
    --package test/fixtures/package_pins/waiver_no_owner/simple.sdn
PIN fixture-core critical explicit=true deps=1 waivers=0
SUMMARY ... waivers=0 ... waiver_without_owner=0 waiver_without_expiry=0 waiver_expired=0 parse_fail=0
```

`waivers=0` with `parse_fail=0` and no `MissingField` error means
`_parse_waivers` (`src/compiler/00.common/assurance/package_pins.spl:287`)
found no `assurance.waivers` node — the checker logic below it is never
reached. The three detections are therefore not "broken rules", they are an
input that never arrives.

## Unresolved, and where the next session should start

A direct probe against `std.common.sdn.parser.parse` could not retrieve a
nested sequence key at all — `project.dependencies`, `assurance.waivers`, and
both with the names swapped, all returned the parent map but no child key —
while the census, parsing the same shape from a real file, does report
`deps=1`. So the probe and the census disagree, and until that is reconciled
the SDN parser has not been convicted. Reconcile that first; do not "fix" the
waiver rules, which are probably innocent.

Probe text was dumped and verified byte-correct, so the discrepancy is not the
fixture construction.

## Second overflow, same class as the fixed one

A scratchpad script importing BOTH `std.common.sdn.parser.parse` and
`std.io_runtime.read_file` still aborts with `fatal runtime error: stack
overflow`. `1ca19a1e31a` fixed the `io_runtime`/`file_ops` `file_read` pair; it
did not fix the general resolver defect (`compiler_cross_module_private_symbol_collision`),
so other colliding pairs remain latent process-aborts. This is a live example.

## Resume

- **Owner:** Phase 5 loader lane (`72ddebf2094`) and Phase 8 assurance lane (`2db75e0d35a`); the SDN question belongs to the sdn/parser owner.
- **Command:** the census invocation above, plus `sh scripts/check/check-critical-package-pins.shs` in a clean worktree.
- **Done when:** both gates print a `PASS —` verdict line, and the waiver negatives report non-zero counts.
