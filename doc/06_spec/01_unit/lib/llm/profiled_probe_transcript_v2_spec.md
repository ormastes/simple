# Profiled combined transcript policy V2

AUTHORED_NOT_RUN. Cases call the production DATA parser, preserve exact acceptable text and refuse empty/control/diagnostic ambiguity. Actual opaque evidence is separately validated against the original canonical capture tombstone before parsing. These tests do not fabricate an evidence owner or assert separate stderr EOF, owned reaping, WAL publication, real cancellation or runtime qualification.

Collector cancel routing (PROBE-UPPER-CANCEL-02): an Err reply to an issued Wait/Logs Begin moves the phase to `<action>-begin-unresolved`, and closing then routes `Step(action, true)` through the exact canonical capture instead of `WorkflowCancel`; a Begin that was never issued (plain `-begin`, before/after/evidence) still routes `WorkflowCancel`. Pure routing only: first_error preservation, owner-side Pending retirement and native partial-begin faults are not exercised.
