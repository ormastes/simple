# Target 6: driver cold HIR receipt capture (2026-09-29)

The production driver now retains compact typed HIR ABI receipts at both
successful phase-3 boundaries. The streaming path captures them before source
reclamation; the retained path captures them after hardening. Warm routes and
non-SCV compiles do not read the inventory for this handoff.

The capture uses the phase-1 SHA-256 source owner and a retained byte length.
This is necessary because nonstreaming low-memory compilation can reclaim
source text after parsing and before HIR lowering. It avoids reopening every
snapshot file or hashing its text a second time at the HIR memory peak. The
current immutable SCV inventory digest, frozen path, source digest and length,
lowered module, and typed ABI encoding must agree before a receipt survives
source/HIR eviction. Duplicate physical aliases produce one receipt; an entry
closure may cover fewer sources than the full frozen inventory.

## Focused evidence

- No-stub Stage-2 native build of
  `test/01_unit/compiler/cache/cold_hir_admitted_entry_seed_spec.spl`:
  305 compiled, 0 failed. Native execution: 3 examples, 0 failures.
- No-stub Stage-2 native build importing the driver through
  `test/01_unit/compiler/driver/hir_function_count_spec.spl`:
  851 compiled, 0 failed after the low-memory correction.
- Both builds use the isolated Stage-2 capsule under
  `build/bootstrap-target56/phase2-runtime-capsules/5d71c26b371b83d0041e10b815dae153a38b9f7c61aa0931f3473aaee919e2f6/`
  and an explicitly hosted runtime archive. This is focused native evidence,
  not a Stage-4 or release qualification.

The driver-import fixture reported a replacement-count assertion failure when
executed before the low-memory correction (4 examples, 1 failure), despite a
successful native compile. It does not exercise the cold receipt handoff; no
baseline or corrected execution result for that assertion is claimed.

`direct-env-runtime-guard.shs` passed on working and staged files, the
generated-spec layout count was zero, and `git diff --check` passed. The
worktree has no `bin/simple` or Stage-4 release binary, so this turn cannot
claim the full compiler/lib/MCP check matrix.

## Remaining production work

Attach actual codegen archive outputs to these receipts, publish the verified
V3 scoped graph after persistence, complete the full CLI cutover and native
warm/cold time-RSS proof. This receipt handoff alone does not establish a
Target 6 performance result or completion.
