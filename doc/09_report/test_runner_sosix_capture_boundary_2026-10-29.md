# TestRunner SOSIX capture boundary

The asynchronous runner previously obtained a platform-specific launch plan
from SOSIX, then chose between raw asynchronous spawn and Windows redirected
spawn itself. `sosix_test_spawn_capture` now selects and executes that plan.
`spawn_tracked_test_process` retains scheduler admission and token registration;
Windows admission denial remains -3, POSIX admission remains blocking, and a
failed spawn releases its slot. The existing public lifecycle helpers remain
available to their callers.

This is a hosted SOSIX dispatch boundary. `io.process_ops` still owns POSIX PIDs
and Windows tagged JobObject tokens. It does not add POSIX process-tree
containment or migrate synchronous/container execution, polling, and cleanup to
a new HAL provider. Those remaining direct imports must not be presented as a
completed HAL migration.

## Verification

- Existing SOSIX process-plan spec: 2/2 passed using the explicitly authorized
  existing Rust bootstrap seed as a diagnostic, with `SIMPLE_LIB` set to this
  isolated worktree's absolute `src` directory. No Phase 2 rebuild occurred.
- Luna independently reviewed admission/dispatch behavior and ran real child
  exit propagation (2/2) plus the new special-argument/stdout/stderr capture
  regression (1/1), all against the isolated source tree using the authorized
  seed diagnostic. Native Windows execution remains unqualified.
- Native core smoke was attempted against the existing pure-Simple release
  binary; its `42` eval produced empty output and failed before patch behavior.
- Native MCP smoke was attempted; its wrapper-selected runtime failed parsing
  the existing Windows redirected-process conditional (`expected Fn, found
  Colon`). These results do not qualify the change for native execution.
- `git diff --check` passed; no executable specs reside in `doc/06_spec`.
