# Bootstrap session containment

Scope: the canonical macOS Stage 2, Stage 3, and Stage 4 compilation graph,
reviewed against source revision `771559eabc9`. This contract complements the
sampled RSS watchdog. It does not provide a kernel memory limit or prevent
arbitrary descendants from calling `setsid`.

## Contract and responsibilities

The outer guard creates one session and exports these two values together:

| Variable | Meaning |
| --- | --- |
| `SIMPLE_BOOTSTRAP_SESSION_ID` | Positive decimal session ID allocated by the guard |
| `SIMPLE_BOOTSTRAP_SESSION_EXEC` | Absolute path to the prebuilt `bootstrap-session-exec.c` executable |

The guard compiles and pins the helper before launching work. A private helper
path must remain available until all descendants have exited; do not compile
it in a worker launch path. The guard receipt records the actual SID and helper
digest. It must sample actual `getsid` values, reject an unexpected descendant
SID, and terminate all known owned groups before declaring failure complete.
Those guard changes are a separately reviewed integration dependency.

The helper is a narrow C syscall boundary: validate `getsid(0)`, establish
`PGID=PID` with `setpgid` if needed, then `execvp`. `--check` validates without
changing process identity. `--sid PID...` provides batch `PID SID` rows for the
parent observer; SID zero means ESRCH. Other observation errors fail. It never
calls `setsid`. Missing, empty, malformed, mismatched, or partial contracts fail
before payload execution, with status 125 at the helper boundary. No Rust code
changes are needed for the audited Darwin graph.

`command-snapshot.shs` records `runtime-env-contract:bootstrap-session-v1`.
The SID is allocated after the command transcript is frozen, so its concrete
value belongs to the guard receipt. A shell immediately inside the guard
validates and forwards exactly this dynamic pair across `env -i`. The five
fixed Unix host variables and the explicit command variables remain subject to
the existing exact transcript checks. Both session variable names are reserved:
the writer, independent verifier, and final explicit-env exporter reject any
attempt to set them. A caller cannot replace a validated helper with a command
that unconditionally succeeds. Earlier transcripts without this policy
record fail current verification and must be regenerated.

## Audited graph

```text
bootstrap-from-scratch.sh / admitted resume
  command-snapshot.shs: bootstrap_stage3_run_transcribed (Stage 2, Stage 3)
  bootstrap_native_build_main (Stage 4; env preserves inherited contract)
    outer RSS guard (integration owner; one setsid boundary)
      hermetic transport shell -> env -> compiler command
        Stage 2: admitted seed native-build -> bootstrap_main output
        Stage 3: Stage 2 bootstrap_main, SIMPLE_BOOTSTRAP_STAGE3=1
          bootstrap_focused_native_build -> CompilerDriver
        Stage 4: admitted Stage 3, SIMPLE_BOOTSTRAP_STAGE4=1
          focused driver or native_build_main -> native_build_worker
            app.io.process_ops re-export -> std process_run_timeout_live
              runtime spawn -> sh -> bootstrap-session-exec -> sh/worker
        compiler/linker process_run -> cc/clang, linker, archiver
        compiler/linker discovery -> xcrun, which, shell, chmod
    probes / phase verification / bounded logging
      run-process-group-timeout.shs -> helper -> worker group
      run-process-group-bounded-log.pl -> validation -> setpgid -> payload
```

The focused native-build route directly drives `CompilerDriver`. The general
native-build route uses `native_build_main.spl`'s live runner at its worker
spawn. The app process module re-exports the library owner. The Darwin piped
runtime sets `POSIX_SPAWN_SETPGROUP` and inherits `*_NSGetEnviron()`;
`runtime_legacy_core.c`'s async path forks/execs without changing SID. Owned
runtime adapters use `setpgid`. These group operations preserve the SID.

`driver_aot_native_output.spl` runs cc, ld.lld, and the selected archiver.
`linker/_LinkerWrapper/native_linking.spl` runs compiler/linker drivers and
xcrun/which discovery. No session creation was found in these source paths.
External tool internals are not a kernel-enforced contract; the guard must
still observe them. Rust PTY session creation is outside canonical bootstrap;
the Rust test kill-monitor is outside native-build. Rust guarded-spawn shell
`setsid` paths are Linux-only. This audit does not admit Linux or PTY execution
under the same assumption. Vendor code was excluded.

`portable-session-exec.pl` also honors the pair, allowing a canonical wrapper
to enter a new process group inside an existing guard session. Its identity
query modes remain observational. The bounded collector validates the child's
session and performs `setpgid` before its readiness handshake, then directly
executes the payload. Direct exec preserves its exec-error pipe and receipt
semantics. Its receipt records `process_group=setpgid`; sanity admission
requires a currently valid session contract for that mode.

The live runner records its worker PGID as before. Under this contract its
failure cleanup sends TERM then KILL to that group, never to the enclosing
guard session. Workers creating further groups are cleaned up by the outer
guard when the bootstrap command terminates. This is not an independent
arbitrary-process-tree cleanup guarantee for the inner timeout function.

## Evidence and remaining gates

On Darwin, the focused contract test passed 21 assertions: session admission,
distinct worker groups in one SID, normal exit preservation, invalid/partial
contracts, the emitted Simple launcher shell, successful setsid followed by
admission rejection, batch SID observation, argument bytes, and timeout cleanup
of a TERM-resistant descendant. Twenty helper launches took 0.059 seconds.

The existing bounded collector contract suite passed under the session
contract, including exec-failure receipt fidelity and cleanup. The new
transcript integration test passed with an unrelated inherited variable
removed by `env -i`. It also rejects the exact SID=1/helper=/usr/bin/true attack,
each single-variable override, and handwritten transcripts carrying overrides.
Running that adversarial test against the original `822d2158865` command owner
fails because the explicit session override is accepted, demonstrating the
regression test distinguishes the vulnerable implementation. Transcript
refusal diagnostics passed.

The existing transcript argv parser test fails `malformed unrelated argv
prefix was accepted` on both this change and the untouched base. That separate
failure is not repaired here. No source-matched Simple binary was built or run
in this lane. The Simple function's emitted shell was exercised, not its
compiled control flow. Required compiler/lib/MCP checks and source-matched
native semantics/performance remain pending; no compiler performance or full
verification PASS is claimed.

Previously built Stage 2/3 binaries still contain their old live runner and
cannot be admitted merely because these source files changed. Rebuild or bind
an artifact receipt proving this implementation before executing those routes.

## Residual race

Polling cannot observe a child that forks, calls setsid, and loses its
discoverable parent between samples. This helper rejects mismatched sessions
at cooperative launch boundaries; it does not intercept arbitrary syscalls.
Unexpected SID observation is a failing run, but an unobserved escape remains
possible. PID reuse, cleanup ownership, root anchoring, sampler stalls, and
maximum sampling cadence remain guard responsibilities. Neither a strict
6 GB ceiling nor a guaranteed 100 ms worst-case observation interval follows
from these changes.
