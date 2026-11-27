# Item 5 Stage 2: method_calls_literals exceeds the native worker deadline

Status: OPEN. Two measured 300-second failures; no Stage 2 admission.

## Observed failure

On Windows with Ubuntu WSL, the frozen release source
`41d9151614adbaadb098b871894537e90593a70f` reached canonical Stage 2 native
compilation after preflight passed all five checks. The Rust seed was used
only as a bootstrap producer. LLVM was 23.1.6; the native build used two
workers, an ext4 source snapshot at the original source path, and the retained
producer-scoped cache on D:.

Both attempts reported this actual failure:

```text
src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl: timeout (300s)
```

| Attempt | Compiled | Reused | Actual timeout | Not attempted |
|---|---:|---:|---:|---:|
| First native build | 1254 | 0 | 1 | 362 |
| Canonical single cache retry | 129 | 1252 | 1 | 235 |

The reported failure totals were 363 and 236 respectively. Deferred files are
not independently reproduced compiler defects. Do not add compiled counts
across attempts to infer a unique-object total.

The outer Stage 2 launch exited 1 after 3570.58 seconds. Its watchdog recorded
quiescent=1, no unexpected session PIDs, and peak RSS 2571140 KiB. Source HEAD
was unchanged. No admitted compiler, sanity/Hello receipt, or Stage 3 pass was
produced. This is a deadline failure, not evidence of an out-of-memory event.

## Preserved evidence

Host-local archive, not a published CI artifact:
`build/review/item5-current-bootstrap-41d915-20261107/stage2-timeout-attempts-retained/`.
The archive contains both logs, their watchdog receipts, the outer terminal
receipt, and a SHA-256 manifest. Selected hashes:

| Artifact | SHA-256 |
|---|---|
| first.log | `2ab01634a60d481e8d95d55b3307f0f6be02c19837599005f36ecbdfb19761f3` |
| retry.log | `d7ebc2888d8e4ca5a99879faaa2c1e842f4ed7d630897e188e4446b2ea066f17` |
| terminal.json | `944e16380763452103647d63b1aa5db2f6a8a1f01b64a498c4b4a356c40b2766` |

## Recovery and limits

The canonical script supports `SIMPLE_NATIVE_FILE_TIMEOUT`, records its
`--timeout` argument, and retains source/runtime admission checks. A subsequent
900-second recovery was launched with the same source, producer and cache.
Its result is not established by this report. Increasing the deadline is a
bounded workaround, not a performance fix or bootstrap qualification.

Preserve `NativeCompileAdmission`: after a timeout, dropping a Rust worker
handle cannot cancel the worker, so new files must not be admitted into that
attempt. Do not disable containment, erase caches, or mark deferred files as
passing.

Later release changes `74bf9d08fe0` and `84e362e460b` touch the affected source
but address tagged text handling and GPU dimension validation respectively;
neither is established as a fix for this timeout. The separate unresolved
enum helper warning has a matching landed fix, `40c2ce3d9ca`, and must not be
conflated with this deadline failure.

Closure requires a completed native build and actual compiler execution with
canonical admission evidence. Full Item 5 qualification still requires the
remaining bootstrap stages, real scalar/vector DB and live HTTP execution,
matched performance, and image/dynamic-provider checks.
