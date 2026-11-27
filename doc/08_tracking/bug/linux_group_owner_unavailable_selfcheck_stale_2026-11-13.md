# runtime_linux_group_owner_unavailable_selfcheck.c no longer builds standalone

- Date: 2026-11-13
- Severity: P3 (advisory bootstrap-tier gate only; no product path affected)
- Gate: `process-v4-group-admission` (`config/check/must_check_gates.sdn`, advisory),
  last stage of `scripts/check/check-process-v4-group-admission.shs`

## Symptom

```
clang-23 -D_GNU_SOURCE -std=c11 -O1 -Wall -Wextra \
  src/runtime/test/runtime_linux_group_owner_unavailable_selfcheck.c
runtime_linux_group_owner_impl.h:1257: use of undeclared identifier 'POLLIN' (and POLLHUP, struct pollfd, poll)
runtime_linux_group_owner_impl.h:1289: call to undeclared function 'owned_adapter_fill_reserved_values'
```

Adding `<poll.h>` and a local copy of `owned_adapter_fill_reserved_values`
compiles it, but the link then needs `rt_array_new`, `rt_array_push`,
`rt_array_free`, `rt_value_is_int`, `rt_value_as_int` and the three
`rt_process_stream_*_v2` owners. Since 72d40515db5 / b536cf56447 the impl
header depends on `runtime_process_owned.c` and the array runtime, so the
harness needs a stub set like `runtime_process_group_retire_linux_selfcheck.c`.

## Why the gate was reordered

The gate is `set -eu`, so this stage killed it before the V4 lifecycle and
ProcessGroup retirement selfchecks ran. Those two now run first and pass;
this stage still fails until the harness is repaired.

## Fix

Give the selfcheck the stub set it now needs, or make the impl header
self-contained (`#include <poll.h>` and a declared helper), then rerun
`sh scripts/check/check-process-v4-group-admission.shs` to exit 0.
