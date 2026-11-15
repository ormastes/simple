---
name: spipe-loop
description: Run a bounded SPipe check-and-repair or daily-debug evidence cycle.
---

# SPipe Loop

For Simple test binaries, first trace the
[existing native runner and listing behavior](../../wiki/simple_native_test_binaries.md).
Repair that workflow using actual build/run evidence. Do not invent an
aggregate registry or listing flag, or infer a foreign framework dependency
from a comparison such as "like GoogleTest".

Run one finite discovery/build/test inventory through all independently runnable
rows, recording every failure rather than stopping the whole workflow at the
first one. Group failures by cause and delegate independent repairs to parallel
agents with explicit file/cache ownership. Let healthy sibling jobs finish;
missing prerequisites block only their dependent rows.

Treat this as the common build-fix strategy: route memory/performance defects
to a separate repair owner (using the requested model, including Astra when
selected), continue independent logic/object discovery, and retain an exact
failed-object ledger. User-authorized optional diagnostics may be disabled or
nonblocking; incomplete measurements, crashes and failed tests stay explicit.
Do not restart healthy jobs just to apply a future checker setting.

Follow the [build/debug continuation guide](../../wiki/build_debug_continuation.md).
Record scoped user-authorized time, memory or other checker bypasses in separate
DIAGNOSTIC attempts with resource/progress monitoring, preserved failed receipts
and unchanged truthful identity reporting. Reuse authorization already given;
restore normal checks before formal admission or promotion. A new compiler must
compile Hello World and execute its output successfully before its next
provisional phase, even when full verification continues in parallel.

Keep the repair budget finite per cause; record explicit user-directed extensions
without inferring unlimited retries. Recheck changed or failed evidence only;
reuse unchanged green results and stop at convergence. A final inventory can
aggregate those results without rerunning a whole passing suite. Never poll
indefinitely, repeat identical failed commands without a changed input or
diagnostic hypothesis, or report missing/zero-test evidence as PASS.

The default continuous mode remains fail-closed unless the host provides an
implemented scheduler. Completing a finite runnable graph is not an infinite
continuous mode. Daily-debug ingests one dated batch, classifies and routes its
causes, records terminal outcomes and exits. Report remaining failed/blocked
rows and exact resume inputs; a diagnostic exception is not formal success.
