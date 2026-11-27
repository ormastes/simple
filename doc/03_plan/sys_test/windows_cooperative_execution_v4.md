# Windows cooperative execution acceptance inventory

All authored specifications are NOT_RUN. Native campaign remains closed.

| Criterion | Authored evidence | Remaining qualification |
| --- | --- | --- |
| Explicit command/environment bounds; Unicode and duplicate keys | Nine `windows_command_owner_v2_spec` pure cases | Actual child environment/argv |
| Expiry immediately before create/resume; timeout at uptime zero | Production clock/timeout helper assertions | Native suspension/resume race |
| Commit before effect; prepare before create; exact intent before start | Six signed-journal `host_execution_windows_progress_v4_spec` cases | Actual protected Windows journal and Docker |
| Cancellation/expiry retains executing capacity | Same signed-journal scenarios | Native child/tree cancellation and retryable cleanup |
| Finite API uses same command reducer | Signed finite Windows scripted scenario | Existing runtime suite NOT_RUN |
| Current writer drift retains cleanup; no archive through stale writer | Source implementation | Native fault-injection NOT_COVERED |
| One-use exact inspected parent capability | Source private marker, native-only mint | Replay/expiry/wrong-target native scenarios NOT_COVERED |
| Persistent common server consumes turns without blocking its poll | Windows lead owns generic smux V5 integration | Configured server acceptance NOT_RUN |

Native inventory for the admitted Windows runner: successful empty/nonempty
stdout/stderr; UTF-8 split across chunks; output bound; expiry before create and
between create/resume; assignment and resume failures; terminate failure with a
live child and after terminal observation; each handle/allocation release failure;
provider replacement; nonmatching labels/TTY/native ID; stale journal/current
policy; disconnect/cancel during each stage; exact creation intent persistence
before start; unknown create result never replayed; one-use marker aliases;
plan-to-bind requires new inspect. These are requirements, not authored passing
fixtures. They must not be counted toward coverage until implemented and run.
