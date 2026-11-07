# Resident Windows GDB owner

Status: isolated implementation candidate; native qualification pending. Clangd is a distinct open provider. The diagnostic backend probe is not evidence for persistent debugging.

The command budget includes delivery: one immutable tokenized frame is offered
through bounded partial writes using byte offsets, while stdout is drained.
Pending writes retain the same frame and offset until actual progress is
reported. A single six-second monotonic deadline covers delivery and response
processing; a separate iteration limit is a backstop, not a second budget.
Cancellation waits at most 100 ms for the operation event and observes the
result without an indefinite wait. Unconfirmed completion retains the native
slot, copied bytes, event and OVERLAPPED storage. Close may terminate the owned
process tree and retry cancellation after its finite exit wait. It reports
cleanup failure rather than reusing storage still referenced by pending IO.
These are source contracts pending actual full-pipe, partial-read, UTF-8 and
cleanup controls; an authored fixture is not runtime qualification.

Inspection authority is enforced by GDB policy, not inferred from accepted
command text. Each serialized session scope captures and verifies the actual
`may-call-functions`, `may-write-memory` and `may-write-registers` settings,
disables all three for inspection, and restores the captured values on success
or error. A newly created session first disables and verifies inferior calls.
Explicitly authorized semantic expressions may enable calls only within their
scope and do not override a pre-existing no-write policy. Execution controls
retain their existing authorization. A per-session reentrancy guard and the
frontend's sole request thread prevent interleaving scopes. Unsupported policy,
failed verification, exhausted shared command deadline or uncertain restoration
retires the native owner; cleanup debt remains blocked rather than reusable.
The C macro and C++ overloaded-operator fixtures must prove unchanged target
state for passive requests, successful authorized semantic control where
supported, exact prior-policy restoration and isolation across two sessions.
These native controls remain unexecuted.

## Boundaries and authority

The long-lived MCP frontend owns every Windows GDB pipe. Its existing serialized request loop is the sole reader, writer and state committer. Eight bounded primitive-array slots hold IDs, PIDs, tokens, partial lines, console capture, target state, last stop/revision, inferior identity, program/build identity and cleanup failure. No mutable Dict is used for session authority. GDB pipe handles/PIDs never cross a worker/process/MCP boundary. The inferior PID copied from MI is target identity for evidence, not an adopted pipe handle.

| Boundary | Transfer and access |
|---|---|
| MCP arguments | Strict JSON decoded once into immutable typed values; encoded copy |
| Admitted GDB image | Frozen manifest pin; descriptor identity/metadata plus terminal byte validation |
| GDB stdin/stdout | Bounded encoded copies; one frontend process owns native pipe handle |
| MI parser helpers | Pure immutable scanner calls; no shared parser Dict or mutable IO owner |
| Local launched inferior | GDB/job-owned child tree; execution effects authorized before command |
| External attach/remote target | Caller-selected target/control relationship; not adopted as a frontend pipe owner |
| Session lookup | O(8) ID lookup; new monotonic IDs on reuse; no stale handle resurrection |
| Existing batch workers | Remain separate manifest-pinned native executables; no persistent GDB handle transport |

The existing GdbMiClient/DAP adapter was inspected. Its shell/FIFO transport does not supply a Windows owner and its mutable Dict result parser is unsuitable for native session authority. The resident transport reuses the in-tree byte-safe MI scanners and adapts values to immutable JsonValue arrays/objects. A narrow shared unescape repair consumes literal backslashes once so Windows paths do not become control characters.

## Dispatch and state

Windows session/workspace/debugger tools dispatch directly to the resident owner as typed Result handlers. Existing Linux/POSIX worker paths remain. The SDK opt-in Result API converts Err to MCP result.isError while old text-handler callers retain their API. Clangd tools return an explicit typed capability error until their separate resident provider exists.

One token may be outstanding per session. Complete lines are assembled with an incremental scan offset and one-MiB framing/capture bounds. Matching results acknowledge a command; async running/stopped/thread-group records update target state. A stop revision prevents an old stop satisfying a new run/step. A new stop arriving before the command's running acknowledgement remains authoritative. Recoverable MI command errors preserve the process. Wrong/late token, malformed EOF, capture or missing-result deadline failures retire the owner and retain failure/cleanup debt. Pending target execution may return state=running after the finite stop-wait budget; it never fabricates stopped.

DebugServiceV1 authorization precedes target effects, with existing operation/perturbation and raw-command policy. Newline/control and script/interpreter escapes cannot cross the raw console boundary. File, args and run remain separate debugger operations; no transactional rollback is claimed. The loaded program/build identity commits when symbols load succeeds even if a later launch stage fails.

Normal close requires gdb-exit acknowledgement, full stdout EOF, actual OS exit status before handle close, and successful native close. The additive v1 receipt distinguishes pending/error/actual exit; Windows exit259 is not confused with STILL_ACTIVE and POSIX ECHILD is not invented exit0. A failed close retains the slot/PID and binding, preventing reuse. EOF shutdown collects all finite owners and propagates failure.

## Startup, hot paths and invalidation

Startup lazily constructs schemas and admits the exact native manifest without starting GDB or compiling source. Artifact hashing occurs at admission/terminal validation; per-tool admission checks descriptor metadata. Interactive resident tools do no directory discovery, source compilation or worker startup. GDB starts only for an explicit session create and remains in that frontend. Query lookup is bounded, and each request has finite read/record/capture limits. Metadata/identity drift invalidates admission; source/binary changes require a new frozen bundle and process. No hot reload, raw-source fallback or old-runtime substitution exists.

Target correctness and latency/RSS are unqualified. Record cold startup, session-create cost, warm stopped-frame/local requests, deliberate running/interrupt latency, EOF cleanup, full process-tree peak RSS and the exact native/runtime/manifest hashes. The three-second command/stop polling budget and eight-slot limit are implementation bounds, not measured performance claims. A bounded command loop may include actual native close's separate five-second reap bound; aggregate EOF cleanup is finite across eight owners and external qualification timeouts must retain failures.

## Required evidence

Compile the debug-info C fixture and native frontend against the new runtime owner. probe_resident.py requires the installed real GNU GDB18.1 hash and tests two actual inferiors, pending breakpoints, launch/stopped frames, locals, read/write-and-restore memory, registers, step-in/over/out, target exit, running/interrupt, EOF/OS exit0, stale IDs and no descendant processes. It never invokes backend_probe. Native MI fault controls separately test token mismatch, deadline, partial EOF/UTF8, stop ordering/freshness and recoverable errors; they cannot prove real target functionality. Attach/remote targets and Clangd remain separately qualified work. No release PASS is implied by source or syntax checks.
