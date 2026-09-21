# Stage 2 command transcript refusal lacked a useful reason

The bounded replay at `1d9860a178052f2aa0b8d987b5f6b735fb9c311b`
recorded `status=complete`, `reason=child-exit`, and `raw_status=1` in
`build/review/stage2-hir-replay-1d9860a-llvm23.receipt`. Its captured log
reported `bootstrap-transcript-error: could not write command transcript`
before the native build. The temporary transcript was removed, so that replay
does not prove which writer predicate failed.

The later `candidate_frontend_smoke` line reporting raw `rc=139` belongs to
stale artifact inspection after this refusal; it is not the exit status of the
replayed native build. No new native build was admitted in this attempt.

The writer now reports bounded reason codes for cwd, Windows required variable
names, environment syntax and duplicates, separator and executable omissions,
newlines, and output create/write or rename failure. Diagnostics expose no
environment values, command arguments, or filesystem paths. The existing
fail-closed return behavior and transcript format remain in force. A focused
unit script covers refusals and valid Linux and Windows transcripts.
