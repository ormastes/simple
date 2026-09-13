# Stage4 leak-check owner imports

**Status:** OPEN (unverified 2026-09-12)

## Reproduction

After native-safe HIR dictionary counting landed, Stage4 stopped with two real
HIR diagnostics in `src/compiler/tools/leak_check/main.spl`: unresolved
`interpret_file` and unresolved `MemLeakEntry`.

## Cause and fix

The tool imported both names through broad, multi-hop facades. Entry-closure
HIR lowering did not recover their defining owners through those chains. The
tool now imports `interpret_file` from
`compiler.driver.driver_public_interpret_bridge`, `CompileResult` from
`compiler.common.driver_core_types`, and `MemLeakEntry` from
`std.mem_tracker.types`. Adjacent memory-tracker operations remain on their
implemented public facade.

## Regression evidence

`leak_check_owner_imports_spec.spl` locks the concrete call/type owners and
rejects the two former facade import shapes.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
