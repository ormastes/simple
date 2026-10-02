# Shared mail helper native build exceeds bounded verification window

Status: OPEN; blocks the compiled shared-SDN bridge acceptance, not a runtime
PASS. Phase1 bootstrap-tool execution was explicitly authorized for this run.

The isolated Linux/WSL Debian build used producer SHA-256
`4ad9c9f7444e625b384f5ceb6ea3144b126e5fc892a6e14e811313ba6f7c2992`
and source `6db50fdf16` plus canonical nested email parser `18fe363b94`.
The source was archived into a private D-drive directory and committed with
Linux Git as `53002a25475634f052673f89bdd07700069e6033`; production worktrees
and shared caches were not modified by the build.

Invocation:

```
SIMPLE_SCV_INVENTORY_COLD_INIT=1 <producer> native-build
  --source src/compiler --source src/app --source src/lib
  --entry-closure --entry src/app/mail_credentials/main.spl
  --strip --output <private-output>/simple-mail-credentials
```

Attempt 2 ran inside a dedicated cgroup with memory.max=2147483648,
memory.swap.max=0, pids.max=512, one CPU and a 300-second timeout. It exited
124, peaked at 344522752 bytes, and recorded no OOM. The last diagnostics were
module-import warnings; no executable was produced. Approximately 250 CPU
seconds were consumed. The exact compiler hot path is not established by
these diagnostics, so this is not evidence of a specific compiler defect.

Attempt 1 did not compile: it failed SCV cold-inventory admission. Its source
extraction was not yet complete and it is excluded from pinned-source evidence.

Retained local evidence:
`D:/dev/mail-config-native-6db50/evidence-attempt2/` contains producer hash,
stdout/stderr, exit, memory peak/events and remaining-process receipt. The
hard-cap launcher is adjacent as `run-native.shs`.

Next action: establish a supported narrower native entry closure or diagnose
the cold-inventory/startup path under the same resource ceiling. Do not rerun
the identical full-root command or claim deployment until the compiled helper
passes the actual CLI fixture.
