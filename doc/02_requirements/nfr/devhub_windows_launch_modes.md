<!-- codex-design -->
# DevHub launch mode constraints

Admission remains fail closed on stale artifact hashes and invalid receipts.
Unsupported loading performs no runtime probes, retries, or network calls.
Existing invocations retain ordinary selection. Only a leading `--mode VALUE`
or `--mode=VALUE` is consumed; CLI selection overrides `DEVHUB_MODE`.
Dispatch preserves argument boundaries and child exit status. Diagnostics go
to stderr, leaving application stdout usable. No latency target is claimed
for a loader that does not yet exist.
