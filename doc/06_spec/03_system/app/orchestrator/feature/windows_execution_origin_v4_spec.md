# Windows execution origin isolation V4

Status: **AUTHORED_NOT_RUN**. No test, build, child launch, native command,
allocation fault or handle-cleanup campaign was executed.

Source: `test/03_system/app/orchestrator/feature/windows_execution_origin_v4_spec.spl`.

REQ-WINDOWS-ORIGIN-001: scripted/native execution origin cannot be substituted
before canonical registry access or command progression.

REQ-WINDOWS-ORIGIN-002: immutable provider policy and managed scope must match
the original progress owner; rejection must leave its canonical state usable.

REQ-WINDOWS-ORIGIN-003: a host continuation cannot use an unrelated live journal
writer, even if the two fixtures describe identical Windows host scope.

| Scenario | Assertions |
|---|---|
| Scripted progress into native provider | Explicit origin mismatch, no operation result, original scripted engine/image commands remain consumable once |
| Changed engine policy or bound managed scope | Provider-domain mismatch, no foreign script consumption, original completes normally |
| Native-origin prelaunch progress into scripted provider | Actual Windows thread admission required; mismatch preserves zero scripted cursor; original cancelled/released before any native command poll |
| Different actual signed journal writer | Origin mismatch retains continuation; second journal remains admitted; both cursors stay zero; original cancels normally |

The first two cases use genuine scripted provider continuations rather than
decoded or manufactured progress. The journal case uses actual signatures and
independent Linux-backed shared journal writers; Windows provider responses
remain explicitly scripted.

The native-origin case requires an actual Windows host and canonical native
thread admission. On a non-Windows host it fails with an explicit prerequisite
message; it is not skipped or replaced with a fabricated native success. Native
progress construction obtains no command owner and launches no process. The
case never calls the native provider command poll: cancellation retires the
prelaunch registry state with a blocked operation, never an OK native receipt.

No case qualifies real child execution, inspection-marker trust, native cleanup
or fault handling. Mapping/source review cannot establish those properties.
