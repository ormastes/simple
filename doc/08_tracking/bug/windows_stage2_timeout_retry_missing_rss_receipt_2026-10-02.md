# Windows Stage 2 timeout retry fails before its RSS receipt archive

Status: orchestration fix verified by focused native Windows Job probes;
full producer and product qualification remain pending.

The frozen Windows source `8ac53a35594ae874dd656efe275ba9ff00a435df`
passed its full tracked-tree inventory (140,121 paths, none missing), strict
materialization, native source consumer, and canonical bootstrap preflight.
Four bootstrap Rust build children returned native exit 0. Its Cranelift
Stage 2 compilation used 80 workers, a 1,200-second per-file timeout, and a
separate outer Windows Job with a 7,200-second time bound and 128 MiB log bound.
Those outer limits do **not** establish an RSS limit.

The authoritative native result was:

```text
compiled=1134 reused=0 failed=1 scope=scope-ea2af62ecac16dee
src/app/io/mod.spl: timeout (1200s)
```

This is one compilation failure reported as a timeout. The frozen Rust native compiler starts
the per-file compilation thread and waits with `recv_timeout(1200s)` in
`native_project/compiler.rs`; expiration returns the timeout error and drops
the thread's `JoinHandle`, so the worker may continue until enclosing process
containment terminates it. No per-file CPU or phase metadata was available to
identify which operation consumed that interval. The receiver maps any wait
error to the timeout label, including channel disconnection; normal caught
compilation panics send completion and report their panic separately. The
retained log alone does not distinguish the wait error subtype. The app/io export facade has
78 export lines, below the existing 256-line contention mitigation threshold;
that classification is not proof of the timeout's cause. File-index progress markers arrived out
of order and do not provide cumulative success counts. The bootstrap recognized
the existing single-timeout same-cache retry condition, but failed before that
retry ran: `cp` could not find `stage2-native-build.log.rss.env`. Its verdict and
outer native receipt were exit 89. No link, admitted Phase 2 executable, or
interpreter/compiler product test result was produced. The completed 1,134-file
cache cohort remains preserved; this fix does not claim to resolve the timeout.

The receipt failure had a separate cause. The Windows branch of
`bootstrap_stage3_run_transcribed` executed its scrubbed environment and exited
before the common POSIX RSS watchdog invocation. The retry archive nevertheless
required that watchdog's receipt. The existing watchdog already supports native
Windows Job Object containment and summed member working-set RSS, so making
the receipt optional would hide a missing enforcement boundary.

The repair wraps the existing Windows `env -i` invocation with the canonical
watchdog and its existing policy knobs. Its default cap remains 5,859,375 KiB,
matching the POSIX branch. The guard resolves its compiler through the pinned
transcribed worker `PATH`, before the workload environment is scrubbed. It
retains new/inherited session policy and the mandatory first-attempt receipt
copy. It publishes actual RSS observations, not a synthetic or optional receipt.
The POSIX execution path and archive contract are unchanged.

Focused Windows verification ran under an outer canonical bounded Job, using
the admitted MSVC LLVM 23.1.1 toolchain and a private session-helper cache:

| Probe | Actual result |
| --- | --- |
| Normal transcribed workload | Exit 7; RSS peak 20,532 KiB, cap 65,536 KiB |
| Retry guard limit | Exit 88, `rss-cap-exceeded`; peak 2,620 KiB, cap 1 KiB |
| Nested inherited RSS Job | Actual workload exit 9; peak 21,612 KiB, cap 262,144 KiB |
| Worker environment | Pinned worker `PATH` and `SystemRoot` observed in the body, while ambient caller `PATH` lacked the native compiler |
| Retry evidence | Actual bootstrap copy block archives the first-attempt receipt at its exact retry archive path; its original cap of 65,536 KiB was verified. Missing receipt and injected receipt-copy I/O failure refuse retry with exit 89. This probe does not independently establish byte-exact archive identity. |

All actual RSS receipts identify `win32-job-object`,
`win32-job-object-no-breakaway`, verified helper integrity, and `quiescent=1`.
The inherited probe records `session_mode=inherit`. The enclosing focused-test
collector returned native exit 0. The first focused test attempt had reached
the guard probes but failed on an existing stale assertion expecting a direct
resume call; resume now delegates to `stage3-native-build-worker.sh`. The
regression now checks that actual delegation and the worker's transcribed call.

Host evidence is retained at
`C:/Users/user/.simple/worktrees/simple-windows-phase2/evidence/cranelift-final-source-preparation/`:

- `authorized-producer-repair2.om48wE/producer.log` and `producer.receipt.env`;
- `rss-focused-windows-repair2/focused.log` and `focused.receipt.env`;
- `rss-focused-windows-repair2/bootstrap-rss-retry.3vhZqL/` actual initial,
  archived, and retry receipts;
- `rss-focused-windows-repair2/bootstrap-rss-inherit.UH3hcP/` actual parent and
  inherited-child receipts.

The native compilation log remains under the private
`bootstrap-cranelift80-8ac-final/logs/x86_64-pc-windows-msvc/` output.
No full producer was relaunched during this repair. A later producer attempt
requires explicit bounded authorization and compatible source/producer/runtime
cache identities; a source fix must not be forced into the old cache cohort.
The frozen source lacks upstream #2239, and publication-receipt framing under
draft #2249 is a separate downstream admission concern. Neither is repaired or
qualified by these RSS probes.

The existing Windows Build workflow invokes the retry regression after
attesting LLVM 23.1.1 and configuring MSVC. That regression discovers the new
inherited-Job test with its own evidence parent; the standalone inherited test
explicitly skips non-Windows hosts. CI retains its actual receipt artifacts.
The local green probes were not repeated for this registration-only change.
