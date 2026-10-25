# macOS provisional self-host chain

`scripts/bootstrap/continue-macos-self-host-chain.shs` runs a diagnostic
Stage 2 → Stage 3 → Stage 3 rebuild → Stage 4 compiler chain on Darwin when
the managed bootstrap runner is unavailable. It writes to a caller-owned,
fresh output directory and its adjacent `<output>.process.env` owner receipt.
The chain remains unadmitted and cannot publish or
promote artifacts. Whole-suite testing and GUI verification are separate work.

A run requires the immutable Stage 2 compiler and its canonical command
transcript. Supplying its native-build log and RSS receipt adds completion,
output-path, quiescence, and enforced-limit checks:

```sh
sh scripts/bootstrap/continue-macos-self-host-chain.shs \
  --source-root /path/to/frozen-checkout \
  --phase2 /path/to/stage2/simple \
  --phase2-transcript /path/to/stage2-command.transcript \
  --phase2-build-log /path/to/stage2-native-build.log \
  --phase2-rss-receipt /path/to/stage2-native-build.log.rss.env \
  --runtime-path /path/to/frozen-runtime \
  --sdk-root /Library/Developer/CommandLineTools/SDKs/MacOSX26.5.sdk \
  --deployment-target 26.5 \
  --output /path/to/new-chain-output \
  --backend llvm --jobs 10 \
  --rss-cap-kib 16777216 --timeout-seconds 7200
```

Choose a fresh absolute output path, backend, timeout, and RSS cap for the
machine. Supply the SDK root and deployment target used for this run. When the
Stage 2 transcript records either value, the adapter requires an exact match;
otherwise it records each as caller-provided diagnostic input. It hashes the
SDK's actual `SDKSettings.plist` without treating the installed SDK as a
release-wide canonical pin. The shared bootstrap policy and watchdog reject
RSS caps that exceed the host-derived limits.

`--stop-after-stage3` and `--stop-after-stage3-rebuild` are diagnostic stop-only
options. Their outputs cannot be resumed by this adapter; use the default for
one complete chain run.

The public adapter process becomes the shared watchdog for the entire chain.
Launch it from a clean, unmanaged shell. A public launch with either inherited
managed-session control is rejected before work starts; nested managed launch
is unsupported because the parent forbids descendant session escapes. The
adapter forces whole-session scope for its fresh session. Nested command guards
inherit that verified session. On cancellation, the outer
guard reaps all descendant process groups before returning and records the
result in `<output>.process.env`; require `quiescent=1` and no observer errors
before treating cleanup as verified. Each command retains its selected timeout;
the outer chain also has a finite lifetime of sixteen times that timeout.

The owner snapshots the source and runtime trees, pins the Stage 2 bytes,
transcript, adapter source, native tool environment, SDK settings, and optional
Stage 2 evidence. It checks Stage 2's version and Hello compile/run before
building P3. Each later compiler gets its own version oracle and Hello
compile/run; bootstrap compiler banners must match Stage 2, while the full CLI
Stage 4 must report its `Simple v...` banner. Compiler digests are checked
against the bytes that passed those probes before the next compiler is run.
Stage 3 uses all six roots from the Stage 2 transcript in the same order. A
producer that cannot accept six roots stops before running a compiler; the
adapter never drops a root.

A passing chain proves only that these local provisional artifacts were built
and passed their version and Hello probes. It does not record release
admission, whole-test results, or GUI behavior.
