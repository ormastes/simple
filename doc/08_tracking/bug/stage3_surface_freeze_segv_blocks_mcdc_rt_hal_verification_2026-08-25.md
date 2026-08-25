# Stage 3 surface-freeze SIGSEGV blocks MC/DC/RT-HAL verification

Date: 2026-08-25
Status: open / release-blocking
Owner: compiler bootstrap and HIR surface retention

## Impact

The MC/DC/RT-HAL hardening feature cannot run its self-hosted `check`, `test`,
SPipe, optimizer, or matched performance/RSS gates. AC-13, AC-15, AC-16, and
AC-18 therefore remain unproven; the feature must not be marked complete.

## Evidence

After two compiler defects were repaired, a fresh Stage 2 completed native
build, passed the positional-entry frontend sanity probe, passed the independent
struct-receiver/runtime capability proof, and was admitted. The provenance-bound
one-thread Stage-3 continuation then loaded 992/992 module surfaces, completed
`export_origins`, entered `surface_freeze`, and terminated with SIGSEGV (139).

Measured immediately before failure:

- process: admitted Pure-Simple Stage 2 compiling Stage 3;
- phase: `surface_freeze` after 992 surface aliases;
- wall time: about 158 seconds;
- RSS: about 10,292,620 KiB;
- CPU: about one fully utilized recovery thread;
- log: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`;
- command receipt: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`.

The log also contains many unresolved callable/payload-origin notices before the
crash. No terminal compiler diagnostic was emitted, so it is not yet proven
whether the immediate cause is malformed retained-surface state, origin-table
growth, or a native receiver/ownership fault inside surface freezing.

## Cleared blockers in the same audit

1. Borrow checking referenced `unwind_payload_dest` and
   `unwind_type_tag_dest` from ordinary `Call` instructions. Those definitions
   now belong to `CallTerminator`, and Stage-2 native compilation passed.
2. `FrozenNativeModuleCapsuleBatchV1.find` was mis-lowered to `rt_string_find`,
   whose integer result was dereferenced as a capsule. A uniquely named free
   lookup now owns the cold O(n) batch scan; Stage-2 positional-entry sanity
   passed afterward.

## Unblock condition

Capture a symbolized Stage-3 failure at `surface_freeze`, repair the owner or
receiver fault without weakening the surface integrity gates, then start a new
scoped session and run the canonical admitted Stage-3 continuation once. Do not
retry in this session: the feature reached the mandatory three-cycle cap.

