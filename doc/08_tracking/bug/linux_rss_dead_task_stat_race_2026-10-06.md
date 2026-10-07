# Linux RSS observer dead-task stat race

The canonical repaired-seed build stopped with rss-measurement-failed (exit 89) at peak 2234676 KiB, below its 5859375 KiB cap. The actual stat bytes show a fully dead build_script_bu task in state X, parent 0, group -1, session -1, RSS 0. The observer's unsigned group/session pattern rejected this kernel exit-race record.

Parse the record before inserting it in the live snapshot. Discard X/x tasks only when their recorded RSS is zero. Retain strict malformed-record rejection and reject negative group/session IDs on every live task. Keep the existing complete-record reader, allocation bound, PID binding, reuse-proof starttime, and memory conversion.

The parser regression uses the exact failed-build bytes, a real live /proc record, a multiline command name, a malformed record, negative live group, and a dead-state record with live RSS. All six checks pass. Native linux-proc enforcing watchdog checks report complete/0 below cap, rss-cap-exceeded/88 above cap, and bootstrap-session-escaped/90 for an escaped child. All three report quiescent=1. Evidence is retained under /tmp/simple-rss-dead-task-repair; the original failure remains under /tmp/simple-interpreter-externs-phase1-seed.

No observer backend, resource limit, or observation budget was weakened. The interrupted build still needs a canonical cache-preserving retry; it has no seed handoff or bootstrap admission.
