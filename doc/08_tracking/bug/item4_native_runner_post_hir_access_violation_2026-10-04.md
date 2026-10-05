# Native runner build: access violation after reported HIR completion

Status: **OPEN; crash cause unproven; runtime qualification blocked.**
Read-only investigation against release
`1954a00653625c5188df880dbff15c41918203b7`. The failed attempt compiled older
source `9737d1217bc44439b56bba6c2ef16faaff51bd20`; it does not test the later
loader or generated-source repairs in PRs 2478 and 2479.

## Exact attempt and terminal evidence

Attempt root:
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/phase34-post-link4/cranelift/phase4-test-runner/`.

- `artifact/lineage.env`: producer phase 2, product phase 4, Cranelift,
  requested `one-binary`, 80 threads, `admitted=false`.
- Producer SHA256:
  `776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`.
  Its retained-object Hello result is diagnostic evidence, not admission.
- `owner/build.log`: SHA256
  `47819a89891e0feb382eba726d40e30e39a1dbd2b3aede98112e24ba9a525c5b`,
  independently rehashed. The retained log contains no `[hir-fatal]` records;
  worker progress reports all 660 HIR modules completed, zero failed, and
  660 HIR cache stores. These counters are not test execution evidence.
- The worker exits `-1073741819` (Windows `0xc0000005`, access violation).
  The coordinator's diagnostic renders a large signal number; this is not a
  normal small POSIX signal or a source-level HIR rejection.
- `artifact/result.json` and `owner/supervisor-result.json`: outer exit 139,
  compile exit 139, no artifact hash, unadmitted. The old owner/collector
  processes 37596/22612 were absent at revalidation.
- Collector receipt records the Windows Job cleanup, including its remaining
  `conhost.exe`. It does not provide a fault address or stack. Worker stderr is
  explicitly middle-truncated in the coordinator log. Last printed module
  identity cannot locate the faulting operation.

Do not attribute this crash to the full CLI's unresolved-symbol diagnostics or
to an older LLVM crash from a different producer. A post-HIR stack or equivalent
isolated reproduction is required before selecting a compiler fix.

## Separate CLI dependencies already owned elsewhere

The full-CLI attempt failed with exit 1 and unresolved-symbol diagnostics.
Read-only source/snapshot inspection identified these existing local repairs:

| Existing repair | Evidence and boundary |
|---|---|
| `ca23c08ed347` | Adds physical numbered-library fallback when a frozen tree lacks `src/std`. The failed snapshot contains `src/lib/editor/00.common/types.spl` and its declarations; release resolution cannot reach it via the missing numbered fallback. Do not add editor exports to conceal this selection defect. |
| `13ea66a2ebb` | Tuple `Hash` impl parameters are declared in source but receiver preregistration lowers before their generic scope. Existing focused fix/tests must be reviewed through their owner. |
| `1329a56f3d7` | Separate snapshot logical-alias selection work, relevant to the T32 import. It is not evidence of the runner access violation's cause. |

These checked local commits are not ancestors of release `1954a006536` and
were unavailable from GitHub's commit/PR lookup during this audit. No active
other-session patch, dirty file or cache was folded into the linker lane.
Commit presence and branch ownership do not prove a build process is live.

## Diagnostic prerequisites and limits

The exact attempt used retained cache
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/early-phase4-from-phase2/cranelift/test-runner/cache`.
Its reuse receipt does not establish historical closure identity; automatic
identity revalidation is required. An empty owner lock is not proof of an idle
writer. Preserve the cache and immutable source receipts.

An LLDB executable and symbolizer are installed under `C:/Program Files/LLVM/bin`.
No matching new runner minidump was found in the inspected user CrashDumps
directory. This is not proof that no crash artifact exists anywhere. A debugger
reproduction must establish immutable producer/source identity, an owned writable
cache, bounded resources, and the actual crashing worker route. Debugging only
the coordinator does not automatically trace child processes. Do not refresh
another owner's shared `build/scv` or manufacture an inherited authority binding.

Isolation can be created within this task; it is not inherently a user-approval
blocker. The existing owner launcher uses `FileShare.None` on
`.post-bool-exclusive-owner.lock`. A private cache clone can be made while
holding that exact lease after checking for writers, preserving automatic
identity validation. Read-only cache inventory measured 3986 files and
268257748 bytes; relocation does not promise cache hits.

The stock `scripts/bootstrap/bootstrap-scv-prime.shs` calls `check --help`.
The exact `9737d121...` bootstrap dispatcher has no `check` command, while
`native-build --help` returns before authority acquisition. Neither help route
can prime this compiler-only producer. The supported route is an actual minimal
native build in an isolated checkout, with canonical cold initialization,
private source/SCV/cache/output/temp ownership, producer identity checks and a
1800-second ceiling. After successful canonical admission, a separate warm
debugger replay may proceed with cold initialization unset. Timeout retains
evidence; it does not authorize blind retries or reuse forged bindings.

## Prepared isolation and resource admission result

Preparation subsequently created
`C:/dev/simple-item4-runner-diag-20261004` on its own work branch at exact
`9737d1217bc44439b56bba6c2ef16faaff51bd20`. Tracked source stayed clean; the only
owned source addition is `test/fixtures/item4_runner_diag_prime/main.spl`.
All 3986 cloned cache files matched their donor SHA256 values while the exclusive
lease was held, and that lease was released. No donor SCV state was copied.
Private temporary, user-storage and worktree-storage directories are explicit;
LLVM precedence is pinned. Independent prelaunch review corrected missing
directory creation and an inherited LLVM-prefix override before admission.

The reviewed `build/item4-runner-diag/prime-request.json` SHA256 is
`854999222cc45a1a355bf39b79650e3082320beb470df75e02bbfaa6efb3daf3`.
Its existing Windows Job collector enforces the 1800-second/32-MiB log bounds
and owned-tree cleanup. Compiler threads are one. The shared five-GiB memory
reservation is advisory, not hard RSS enforcement; its legacy metadata records
80 threads, which is explicitly distinguished from the actual one-thread argv.

At `2026-10-04T12:28:28Z`, the one-shot resource reservation returned null.
`build/item4-runner-diag/launch-result.json` records
`NOT_LAUNCHED_RESOURCE_RESERVATION_UNAVAILABLE`, no reservation and no compiler
launch. A subsequent capacity observation found 18.02 GiB free commit and
three existing five-GiB reservations. The helper requires at least 10 GiB plus
those reservations, before any outstanding upstream estimates. No other lane's
reservation was removed and no automatic retry occurred. Preserve this result
and revalidate changed capacity before creating a separately identified attempt.

LLDB initialization was also repaired locally by selecting the already installed
Python313 directory through process-local PATH/PYTHONHOME; no shared tool/DLL
installation changed. LLDB 23.1.2 initializes successfully. Actual worker attach
and fault capture remain UNRUN. A future replay should attach to the verified
worker PID/creation identity within its owned coordinator tree, preserve the
stack/register/module evidence, and use the existing Job owner for tree cleanup.

No build or debugger reproduction was launched during the initial read-only
triage. No independently owned process or cache was changed. Subsequent private
checkout/cache preparation is separate from an executed reproduction.
Required acceptance remains: identify and repair
the actual fault, execute a focused regression with a qualified route, build the
full CLI and runner with complete lineage, then run the pending item4 native
SSpec/core/MCP/coverage/host gates. This report does not close any of those gates.

## Isolated prime execution followup (2026-10-04, 12:48 UTC)

Changed shared capacity allowed a second admission attempt. Collector preflight
returned 126 before creating a target process because its output parent did not
exist. Only this session's reservation was recovered after verifying its exact
lane/start identity and that its supervisor had exited; no other reservation
was changed. The output parent was created before the third admission attempt.
These were three admission attempts, but only one actual compiler launch.

That compiler launch completed at 12:47:23 UTC. The owned collector receipt
records complete/child-exit, native exit zero, and the supervisor confirms its
reservation was released. Build log SHA256:
`8b013eb754a12d7c9d9bfd15e4364ae078e699e8e3c582ecf1e3980eea71f6cb`.
The isolated `prime-artifact/hello.exe` is 1,369,088 bytes, SHA256
`e024e3b173ff744e381a1c423cabcaadd8c2407d2916dca0e9cdfb6fadc8d2e9`.
A separate ten-second-bounded run exited zero with stdout
`item4 isolated prime` followed by a newline and empty stderr. The retained
`build/item4-runner-diag/hello-run-receipt.json` records this execution.

This establishes the minimal cold-prime compile/run using the old immutable
producer and source identified above. It does not reproduce or repair the full
runner crash, admit that producer, or verify newer release source. Debugger
attachment and the full runner build remain pending; preserve the primed
authority and private caches for the next bounded diagnostic.

## Full-runner diagnostic admission followup (2026-10-04)

This sequence is separate from the successful minimal prime and its admission
attempts above. The first two full-runner diagnostic admission requests were
denied; they do not count as compiler execution or crash reproductions. The
third acquired admission, but the launched build Bash process returned exit 1
after approximately two seconds, with an empty collector log. No actual worker
debugger attachment was attempted (`attach_attempted=false`).

Admission success proves only that the request obtained its resource reservation.
The short exit and empty log do not locate a compiler fault, demonstrate HIR
completion, or reproduce the earlier access violation. Empty capture also cannot
prove that the attempted command emitted no diagnostics. Preserve the attempted
command, private output paths and terminal receipts; do not relabel or overwrite
the earlier prime, runner or admission evidence.

Evidence root is
`C:/dev/simple-item4-runner-diag-20261004/build/item4-runner-diag/`:

- `runner-admission2-launch-result.json` records
  `NOT_LAUNCHED_RESOURCE_RESERVATION_UNAVAILABLE`, with no reservation.
- `runner-admission3-launch-result.json` records terminal collector exit 1 and
  `reservation_released=true`; `runner-debug-result.json` records build exit 1,
  null debugger exit, and no attach attempt.
- `runner-collector/collector.receipt.env` records complete/child-exit and
  zero captured bytes. Its empty-log digest is
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The separately owned `echo-forwarding-probe.ps1` used asynchronous BaseStream
copies of both child pipes into the outer collector. Its five-second-bounded
receipt records exit 0 and 114 captured bytes, containing `ITEM4_ECHO_STDOUT`
and `ITEM4_ECHO_STDERR` plus two PowerShell `VoidTaskResult` lines. This proves
small-command stream visibility, not the cause of the earlier Bash exit.
The v2 driver suppresses the task-result values and uses the same explicit
streaming for both build and debugger children, without a full-output buffer.

Prepared `runner-v2-request.json` has SHA256
`5b8aeea583a7988e70edf7a2cd2ccd84a1445ccf2e9159f1fa95dc9087b0ae47`.
The immutable prepared request specifies one actual compiler thread and fresh
output paths. Its advisory memory reservation is not a hard memory limit or
measured peak. The subsequent `runner-v2-launch-result.json`, observed at
2026-10-04T13:26:01.5713804Z, records
`NOT_LAUNCHED_RESOURCE_RESERVATION_UNAVAILABLE`, null reservation and
`admitted=false`. This is the first admission attempt for v2; it did not launch
a compiler or debugger.

The later read-only `v2-post-refusal-admission-observation.json` records a
locked snapshot at 2026-10-04T13:26:39.5357473Z: two existing reservations
(owners 67492 and 43428), both upstream collectors terminal, and free commit
capacity 19,051,814,912 bytes below the required 21,474,836,480 bytes. This is
a later capacity observation, not proof of the exact earlier refusal cause.
Free commit capacity is distinct from the launch receipt's free physical
memory. The observation's private guard was released; other owners' state was
not modified.

The root reviewer also recorded `bash -n runner-v2.shs` passing: syntax only,
without executing the shell body. No further diagnostic attempt is planned
in this wave. The original Bash exit cause, full-runner crash and runtime
qualification remain unresolved; no item4 assertions ran. Preserve all earlier
outputs, prepared request and refusal evidence for a separately admitted run.
