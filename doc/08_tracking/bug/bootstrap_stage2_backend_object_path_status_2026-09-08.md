# Bootstrap Stage 2 backend object-path failure

## Status

Open. Reproduced after two intervening module-surface freeze defects were fixed.
The mandatory three-cycle fix/verify budget is exhausted; do not retry this
rollout without a fresh scoped session.

## Reproduction

```sh
env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 \
  --output=build/image-read-bootstrap-v3 \
  --strategy=normal --mode=dynload --jobs=half
```

## Observed failure

Stage 2 compiles and reaches bootstrap compiler sanity. The positional
hello-world frontend smoke parses and lowers successfully, then its native
compile fails with `backend object-path status 1`. The candidate is rejected;
seed fallback is correctly refused.

Primary evidence:

- `build/image-read-bootstrap-v3/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`
- `build/image-read-bootstrap-v3/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
- `build/image-read-bootstrap-v3/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`

## 2026-09-08 fix cycles

1. The native and Rust backend-plugin bridges called provider diagnostics only
   after success. Both now collect diagnostics after success or failure while
   retaining the primary status. The focused source contract
   `test/01_unit/compiler/backend/backend_plugin_failure_diagnostics_source_contract_test.shs`
   passes. A fresh `v4` run then exposed a separate module-surface failure.
2. `v5` replaced the staged-native-unsafe construction-dictionary `len()`
   check with the established materialized `keys().len()` boundary. It advanced
   to `frozen module surface lookup is incomplete`.
3. `v6` applied the same safe check to the rebuilt frozen lookup. Surface
   freeze, HIR, monomorphization, and MIR then completed, but native AOT again
   ended with `backend object-path status 1` and no diagnostic file content.

Latest evidence:

- `build/image-read-bootstrap-v6/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`
- `build/image-read-bootstrap-v6/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
- `build/image-read-bootstrap-v6/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`

The remaining failure is downstream of MIR and inside the selected backend
object-path session or publication path. No `simple-dynamic-aot-*` or
`simple-aot-diagnostic-*` directory remains under the evidence root or `/tmp`,
so cleanup completed (or the staging path never became observable). A next
session should add scalar stage/status diagnostics that do not depend on the
same file-writing path, then run one isolated cached sanity cycle.

## Impact

No admitted self-hosted runtime is available for compiling or executing the
image-to-Markdown feature tests. This was the third and final bootstrap
verification cycle for the feature session, so it was not retried.

---

## Re-verified 2026-09-13 — now the FIRST blocker, after the staging defect was fixed

This record is no longer behind another failure. The Windows/MSVC Stage 2 lane
reached it again today after a long chain of fixes, and it is now the frontier.

What changed since 2026-09-08, all landed on `main` today:

- Stage 2 link went from **33 unresolved externals to 0** (sqlite closure cut,
  `S_ISDIR`/`S_ISREG`/`__builtin_popcount`, four unimplemented `rt_file_*`
  externs implemented, and two Simple methods that were called but defined
  nowhere).
- The Stage 2 compiler is **built and runs** — `simple-bootstrap 1.0.1-beta.1` —
  and natively builds a hello world by hand (rc=0, exe produced).
- `diagnostic staging unavailable` is **fixed**: `rt_secure_temp_dir` was hitting
  `CreateDirectoryA`'s 248-char directory limit (`ERROR_FILENAME_EXCED_RANGE`,
  206) on a 258-char staging path; it now uses `CreateDirectoryW` with the
  extended-length prefix.

Evidence that this record's failure is what remains, and is distinct:

```
reason-len=30  ->  "diagnostic staging unavailable"   (before, now fixed)
reason-len=28  ->  "backend object-path status 1"     (now)
```

and the staging diagnostic no longer fires at all (0 occurrences of
`rt_secure_temp_dir:` in the smoke log), confirming staging now succeeds.

## What is still missing, and it is the same complaint as 2026-09-08

The reason delivered is still opaque: `backend object-path status 1` is a status
code with no message. `compile_aot_into_path` is handed a `diagnostic_path` to
write a reason into, and that file is either empty or unread — so the caller can
only report the number.

The staging defect above was solved in one run once the failing call was made to
say `GetLastError` and the path it tried. The same move is the obvious next step
here: make the backend write, and the driver surface, whatever it knows before
returning 1. Note the trap that cost time on the staging fix —
`rt_secure_temp_dir` has three byte-identical copies and only
`runtime_secure_staging.c` is the one that links, so instrument the copy that is
actually in the artifact and verify with `strings` on the binary rather than
assuming.

## 2026-09-13: narrowed to "write reports success, file is empty"

Three instrumentation passes landed today moved this from an opaque status code
to a specific, reproducible contradiction. Current state:

```
backend object-path status 1 (diagnostic file empty; path <266 chars>)
```

and **no** `AOT diagnostic write failed` warning, which is now emitted whenever
`file_atomic_write` returns false. So:

- the backend DOES reach a failure path and DOES call the diagnostic writer
  (every one of the twelve failure returns across `compile_ir_to_object_path`,
  `DynamicBackendAdapter.compile_aot_into_path` and
  `dynamic_backend_publish_object_v1` writes one);
- `file_atomic_write` returns **true**;
- the driver then reads the file successfully and finds it **empty**
  (`Ok(message)` with `message.len() == 0`, not `Err`);
- both writer and reader normalise through `host_path_native`, so they agree on
  the path, and both now get the extended-length prefix (the path is 266 chars,
  past the 247 ceiling).

A write that reports success and leaves a zero-byte file is the contradiction to
chase. Candidates not yet eliminated, in the order I would take them:

1. `rt_file_atomic_write` writes to a temp file and publishes by rename. If the
   temp write succeeds and the publish silently no-ops, the destination exists
   and is empty and the function still returns success. Instrument the publish
   step specifically — the temp path is also long.
2. The content argument arriving empty. `backend_aot_write_diagnostic` bounds
   the message with a slice before writing; verify the bounded value is
   non-empty at the call, not just the source message.
3. A cleanup racing the read: `llvm_object_stage_fail` removes its stage dir,
   and the driver removes `diagnostic_dir` after reading. Ordering has been
   reasoned about but not traced.

### Verified NOT the cause (do not re-chase)

- Not MAX_PATH on the directory: `CreateDirectoryA` at 258 chars was real and is
  fixed (`CreateDirectoryW` + extended-length prefix).
- Not MAX_PATH on the file open: a 278-char absolute path round-trips correctly
  through `file_atomic_write` + `file_read_regular_no_follow_bounded` today.
- Not a missing extern registration, not `SystemRoot`, not `--entry-closure`,
  not `--mode one-binary`, not the harness argv — the rejected Stage 2 binary
  hand-builds a hello world at rc=0 under all of those.
- Not a stale object cache: reproduced with `stage2-native-cache` and
  `native-objects-*` deleted.

### Note for the next session

`rt_secure_temp_dir` exists in three byte-identical copies and only
`runtime_secure_staging.c` is the one that links. Instrument the copy that is
actually in the artifact and confirm with `strings` on the binary before
concluding a diagnostic is silent — that mistake cost a full cycle here.
