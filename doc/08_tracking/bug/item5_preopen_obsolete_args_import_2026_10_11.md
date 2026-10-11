# Pre-open native fixture imported a nonexistent module

The de400/Phase2-75c preopen row failed during source closure before HIR:
`unresolved import 'std.sys'`. Watchdog completed with exit 1, quiescent=1 and
peak RSS 2527888 KiB, below the imposed cap. Evidence remains at
`apps-release-20261010-attempt2/preopen/build.log` on the Item5 ext4 volume.

Use the same existing configured-family `std.nogc_sync_mut.sffi.system.args`
owner as the real vector app fixtures. Preserve argument count checks and
trailing positional argument interpretation. Apply the correction to the new
checked-close fixture as well. Both owners call runtime argument retrieval;
this adds no platform branch or new extern declaration.

Existing preopen fixture remains the regression: its six fresh-process policy
refusals/control cases must compile and run with real constructor markers.
Execution is pending a repaired producer; no new passing result is claimed.
