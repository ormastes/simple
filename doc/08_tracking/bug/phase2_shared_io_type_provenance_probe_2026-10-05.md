# Shared I/O type-provenance diagnostic pair

Parent bug: `phase2_subsystem_helper_mir_failures_2026-10-05`.
Status: fixtures authored and statically reviewed; native execution UNRUN.
No production workaround or compiler root fix is established by this change.

`native_shared_io_type_provenance.spl` preserves the failing source shapes:
an inferred static Result factory local, its inferred payload and method
Result, optional `if val` text binding, and a Result-returned nested enum
field comparison. `native_shared_io_type_provenance_typed.spl` adds explicit
Result/payload/enum locals and coalesces optional text to an explicitly typed
empty string. Both are self-contained diagnostic fixtures, not replacements
for process pinning, collection or authority checks.

Both mains implement the same eight numbered checks, return the first failing
number, and print the same success/count line only after all eight succeed:

| Check | Required observation |
|---|---|
| 1 | Positive static factory returns Ok |
| 2 | Payload method returns an Ok array |
| 3 | Array length and both values remain exactly `[5, 7]` |
| 4 | Payload's ordinary instance method returns true |
| 5 | Negative factory input returns Err |
| 6 | Optional nil, empty text and Linux all return false |
| 7 | Mixed-case Windows text returns true |
| 8 | Result<bool> unwrap and nested enum equality/inequality return true |

The typed candidate does not cast enums to integers, bypass Result errors,
drop array checks, or change nil/empty behavior. An original-form failure and
typed-form success under the same producer/backend would justify testing a
narrow source workaround. If both pass, the fixture does not reproduce the
real multi-module failure; no production change is justified by that outcome.
If both fail, preserve each diagnostic and identify the earliest actual owner.

Root composes these committed files into a new complete canonical short source
overlay, using the existing reviewed monitor-only owner/watchdog/collector,
private cache/output/temp and current Phase2 artifact. Compile and run each
backend independently, preserve failures, and record wall time/peak RSS plus
actual process exit and exact producer/source hashes. Do not alter frozen916
or live P3/P4 sources or caches. No P2 rebuild starts from this lane.

After any successful source workaround, retain the original fixture as the
root-fix/removal test. The real production helper and existing six-case
`native_env_platform_optional.spl` still need qualification; this small pair
cannot prove the whole helper closure or process lifecycle.
