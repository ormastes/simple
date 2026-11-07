# Real smux POSIX canonical output helper

Source: `test/03_system/app/llm_caret/feature/smux_runtime_terminal_transport_spec.spl`.
Status: **AUTHORED_UNRUN**. Runtime execution and docgen have not run. This is a
real bounded helper-to-smux transport scenario, not Podman attachment or
authenticated positive runtime binding acceptance.

Run this spec in a fresh isolated POSIX test process. Preconditions are an
admitted canonical process registry, absolute `/bin/sh` and `/bin/sleep`, fresh
entropy and available smux capacity. Missing preconditions fail; there is no
skip-pass or synthetic successful stream. The scenario acquires at most two
of the registry's sixteen slots and intentionally retains both. Do not repeat
it inside a long-lived shared test process.

1. **Spawn a real bounded output helper.** Generate a fresh marker and start
   the shell through `sosix_process_spawn_piped_ref_v1`. It prints a start
   marker, sleeps two seconds, prints a tail marker and exits. Explicit CRLF
   preserves line starts for the raw VT consumer. A second independent real
   shell sleeps six seconds, emits no output and exits without being adopted.
2. **Adopt the canonical reference into the existing smux owner.** Create a
   real vacant pane and use its current epoch, configuration revision and child
   incarnation. No serialized reference or runtime identity is fabricated.
3. **Reject stale close authority while retaining unsupported close ownership.**
   Change only the primary helper's generation and require
   `stale_process_reference`. Validate both original exact registry references
   afterward, without a liveness claim. Reject text/command input before queue mutation and reject changed
   native geometry for the adopted output-only owner.
4. **Poll a fresh output marker through the sole pane reader.** Use normal smux
   polling/capture only and validate the same exact registry reference each turn.
5. **Drain output until observed EOF without inferring process exit.** Require
   both fresh output markers, explicit EOF, unchanged reference and no retained
   read error. Do not call waitpid or infer exit from EOF. Polling has an
   eight-second deadline and at most 400 turns with 20-ms waits.
6. **Retain unsupported POSIX close authority.** `smux_close_pane` must return
   false while preserving the exact pane, window, session and canonical ref.
   Direct canonical close must report `process_close_unsupported`; it must not
   signal processes, close descriptors or free the slot. The unrelated exact
   registry reference must remain valid after this attempt; this is not proof
   of continued process execution. Both original refs must remain valid and
   report exact `process_liveness_unsupported` and `process_close_unsupported`
   errors for liveness and close respectively.

`close_output_transport_fixture` verifies refusal and retained authority; it
does not perform cleanup or claim successful teardown. There are no hidden
signals, cleanup executables, PID fallbacks or close retry loops. Process exit
is test isolation, not proven helper/resource teardown. Error paths may still
retain these two slots and report failure honestly.

**BLOCKED_CAPABILITY:** POSIX process liveness, independently observed exit,
post-exit draining, successful helper/descriptor teardown and duplicate close
rejection after released authority are unavailable. They are not passed
or silently omitted; a separate admitted Windows fixture or a newly admitted
canonical cleanup provider is required for that acceptance.

`PipedProcessRefV1` is process-local registry-lifetime authority. Its PID and
generation cannot be deserialized as authority after restart. Adoption proves
ownership of an output helper, not engine attachment, execution authorization,
interactive support, provider identity or agent readiness.
Validation performs exact registry lookup only, with no read, wait or signal.

Execution remains blocked until daemon canonical registry source, an admitted
runtime and a root-authorized test slot are available. Authored source provides
no passing runtime evidence.
