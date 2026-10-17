# smux Windows actual shared-session terminal clients

**Status: UNEXECUTED.** Authored review manual; SPipe generation, zero-stub
validation, native SSpec execution and watchdog receipts remain pending.

Executable: `test/03_system/tools/smux_windows_shared_clients_spec.spl`.
Native fixture: `test/fixtures/compiler_entrypoint/windows_smux_shared_clients/main.spl`.
Detailed live workflow and bounds:
`doc/09_report/smux_windows_shared_clients_fixture_2026-10-16.md`.

## Required fixture binding

Set `SMUX_SHARED_CLIENTS_FIXTURE` to the actual prebuilt native fixture `.exe`
and `SMUX_TEST_BINARY` to the actual matching compiled `smux.exe`. They must be
distinct existing files. Run the wrapper on native Windows with an admitted
pure-Simple SSpec runner. Missing paths/files, wrong host, provider failure or
absent child output fails; no build, seed fallback, skip or golden-output read
can satisfy the scenario.

Qualify the Phase 2 and Phase 3 cohorts separately. Preserve exact producer,
fixture/product hashes, source and native configured-owner/runtime receipts.
Set `SMUX_SHARED_CLIENTS_EVIDENCE_DIR` to separate cohort artifact directories;
the default is `build/test-artifacts/03_system/tools/smux_windows_shared_clients`.

## Scenario

Requirements: REQ-SMUX-INTERACTIVE-003 (local selection),
REQ-SMUX-INTERACTIVE-006 (detach/sibling continuity),
REQ-SMUX-INTERACTIVE-002 (actual raw Ctrl-C delivery), REQ-SMUX-WIN-003
(independent windows/panes/clients), and REQ-SMUX-WIN-005 (live resize wiring).
Console mode restoration in INTERACTIVE-006 retains its separate native fixture
gate; this wrapper does not claim to replace it. WIN-005 coverage here observes
actual client terminal resize reaching production frame geometry; the existing
owner SSpec's child-computed Console.WindowWidth/Height oracle remains mandatory.
INTERACTIVE-002 Unicode delivery likewise retains its separate native gates.

1. Require native Windows and both real prebuilt executable paths.
2. Call the existing process facade with the fixture executable, the actual
   product as its sole argument and a finite 180000-ms timeout.
3. The fixture launches real owner and two actual interactive clients on the
   same session under independent ConPTY terminals. It observes shared minimum
   geometry and actual terminal resize, local window/pane input destinations,
   small-client detach and remaining-client expansion, raw Ctrl-C child
   interruption, retained child state, exact child exit codes and complete
   acquired-lease cleanup before printing its PASS result.
4. Construct typed execution evidence with `capture_exec_detailed` using the
   observed stdout, stderr and exit status. Construct typed log evidence with
   `capture_log` using the actual bindings and process result. Persist both
   helper bodies even when the observed run fails, so failure evidence survives.
5. Require actual exit code zero, empty stderr and exact stdout
   `Windows smux shared clients PASS` followed by one newline. Only Windows
   CRLF-to-LF normalization is allowed; extra output or whitespace fails.
6. Require both evidence files to be written and read back unchanged. These
   artifact-integrity checks accompany actual process assertions and cannot
   replace them.

**Execution Captures:** `build/test-artifacts/03_system/tools/smux_windows_shared_clients/fixture_exec.txt`.
**Log Captures:** `build/test-artifacts/03_system/tools/smux_windows_shared_clients/fixture_process.log`.
The paths describe future execution artifacts; no such capture is claimed here.
Neither artifact fabricates an internal protocol transcript or cleanup receipt:
the fixture's actual process result remains the behavioral oracle.

## Mandatory outer watchdog and pending gates

Run under an external Windows Job/process-tree watchdog of at most 180 seconds,
with a retained timeout/termination receipt. The process facade's timeout alone
does not prove all descendants are reaped or that a broken FFI call returns.
Timeout, missing outer supervision or incomplete tree cleanup blocks admission.

After actual native execution for both producer cohorts, run SPipe docgen and
the maintenance scan once, preserving actual executed case counts and requiring
complete generated documentation with zero stubs. The authored source/manual
does not establish those gates, pixel fidelity, complete cursor styling,
clipboard behavior or full tmux compatibility.
