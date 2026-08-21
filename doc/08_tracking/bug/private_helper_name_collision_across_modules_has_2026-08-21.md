# Private module helper `_has` resolves across modules — RESOLVED 2026-08-21

- Date: 2026-08-21
- Status: **RESOLVED** (product renames; the compiler-side scoping defect is
  tracked in the 2026-08-17 record of the same name and remains open)
- Predecessor: `private_helper_name_collision_across_modules_has_2026-08-17.md`

This record was filed empty (0 bytes). It is the 2026-08-21 recurrence of the
2026-08-17 defect: a module-private (`_`-prefixed, non-`pub`) top-level `fn` is
NOT private — the interpreter resolves free functions by NAME across every
co-compiled module, so a spec-local `_has` with SUBSTRING semantics is silently
replaced by another module's `_has` with EQUALITY semantics. Exit 0, wrong
answer, no diagnostic.

## Reproduced RED

`test/01_unit/app/build/private_helper_name_collision_spec.spl` —
`3 total, 0 passed, 3 failed` before the change (the count matches the sweep
table in
`doc/08_tracking/bug/light_test_daemon_serializes_concurrent_test_invocations_2026-08-21.md`).

## Root cause

Three same-signature `([text],text)->bool` definitions named `_has` were
co-compiled:

- `src/app/build/targets/change_classifier.spl:56` — EQUALITY
- `src/app/sspec_maintain/main.spl:53` — argument presence
- `src/app/spec_to_sspec/main.spl:45` — argument presence

Because all three share a signature, they never appeared in
`scripts/check/duplicate_pub_fn_baseline.txt` (that census counts names with
>= 2 *distinct* signatures) — so the ratchet could not have caught this, and
the baseline is unchanged by the fix. Worth stating plainly: the dup-name gate
being green is not evidence that name collisions are absent.

## Fix

Renamed each to a module-unique name — `_change_classifier_has`,
`_sspec_maintain_has_arg`, `_spec_to_sspec_has_arg` — with all call sites
updated. No behaviour change in any of the three bodies.

## Evidence

- `private_helper_name_collision_spec.spl` — 3/3 GREEN (was 0/3)
- Neighbours: `private_helper_collision_class_spec.spl` 4/4,
  `build_targets_spec.spl` 34/34, `change_classifier_spec.spl` 8/8

## Still open

The language-level defect — make `_`-prefixed top-level functions resolve
module-locally — is unchanged and lives in the Rust seed's function-lookup
path. Renaming is a mitigation per collision, not a fix for the class.
