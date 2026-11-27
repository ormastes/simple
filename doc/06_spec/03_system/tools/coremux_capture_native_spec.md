# CoreMux native terminal capture

Status: **NOT_RUN**. This manual was authored alongside the executable scenario;
it is not generated execution evidence. Native runner, SPipe generation, manual
maintenance scoring, and terminal screenshots remain unexecuted.

Source: `test/03_system/tools/coremux_capture_native_spec.spl`.

The scenarios require an admitted pure-Simple runner configured for the native
Windows SOSIX provider. It fails on other hosts. The application imports generic
SOSIX interfaces; implementation selection belongs to configuration.

1. Create the real pane owner and launch PowerShell through ConPTY. The child
   writes four red lines into a three-row screen, ending in `COREMUX_END`.
2. Poll the production pane owner for at most 100 attempts. Require the final
   marker and positive actual ingestion/content counters.
3. Close the native owner, retrying deferred teardown at most 100 times. Preserve
   the returned state each time and require successful resource cleanup.
4. Capture the retained terminal history with seven-byte pages. Require every
   page to fit its budget, concatenate the bytes, and compare with the complete
   retained styled capture. Require the first history line, final marker, and
   canonical red SGR sequence.

A second scenario launches a real piped PowerShell child that prints thirty
distinguishable lines into an owner with a three-row screen. It checks the final
marker, closes the exact process handle with finite retries before assertions,
then requires all thirty lines from legacy capture/history. The independent
current-grid capture must retain the final line without claiming the older first
line is still on screen. This is the production regression for tail selection.
It is authored and NOT_RUN, not a passing compatibility claim.

Selected requirements: REQ-CMUX-003/005 and NFR-CMUX-005/007/008. Ingestion here
means delivered decoded-text bytes; it is not a native syscall-byte measurement.

The cursor helper receives explicitly constructed owner/lease identity for this
local composition test. These values do not authenticate a remote client. The
scenario proves neither server admission nor endpoint transport. Those require
the separate real connected-client scenarios.

Related pure controls in `test/01_unit/os/smux_capture_cursor_spec.spl` cover
logical ranges, wrap joining, UTF-8/ANSI byte boundaries, lease isolation,
incarnation and content staleness, expiration, option mismatches, descriptor
capacity, synchronized snapshots, and retained cleanup handles. Those controls
are also **NOT_RUN**.
