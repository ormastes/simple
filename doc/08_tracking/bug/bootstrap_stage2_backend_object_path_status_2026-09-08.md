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

## 2026-09-13, later: the failure is NAMED — `llc not found`

Four rounds of inference failed on this. A temporary unconditional trace on
`backend_aot_write_diagnostic` settled it in one run:

```
aot-diag: called msg_len=13 bounded_len=13
```

`"llc not found"` is exactly 13 characters. That is
`llvm_backend_tools.spl:317`, reached when `find_llc()` returns empty.

So the backend failure is **not** a codegen or object-emission defect at all —
the LLVM object stage cannot locate the `llc` executable. Everything downstream
("backend object-path status 1", "diagnostic file empty") was noise generated by
that one missing tool plus a diagnostic that could not be read back.

### Why it stayed hidden

`find_tool_portable` (`llvm_capability.spl:177`) resolves LLVM tools BY NAME at
run time — `where llc` on Windows, `command -v` elsewhere. The message it
produces on failure was written correctly every time, but the driver read the
file as empty, so only the generic status ever surfaced. The read-back problem
is real and still unexplained (see below); it is what made a one-line cause take
four cycles.

### What was tried and did NOT fix it

`PATH` was added to the Stage 2 canonical env allowlist and passed at the stage
build (this was a genuine gap — the allowlist is the child's entire environment).
The symptom did not change, and `bootstrap_stage_sanity` already receives
`${stage_build_path}` and exports it, so the smoke should have had a PATH. `llc`
itself is present and on PATH for an interactive shell:
`/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin/llc.exe`.

### Where to go next, in order

1. **Find out what `where llc` actually sees inside the smoke.** The tool lookup
   goes through `backend_shell_tuple`, i.e. it spawns a shell. If that spawn does
   not inherit the exported PATH, or `where.exe` itself is unreachable because
   System32 is missing from the passed PATH, the lookup fails regardless of the
   allowlist. Trace the lookup, not the environment.
2. **Give `llc` an explicit override.** `find_nm_portable` already honours
   `SIMPLE_NM`; there is no `SIMPLE_LLC` equivalent. Adding one, and passing it
   through the allowlist, removes the run-time name lookup from the bootstrap
   path entirely — which is the more robust fix regardless of what (1) finds.
3. **Separately**: the diagnostic file reads back empty even though the writer
   reports writing 13 bytes to it. That is its own defect and is what hid this
   for four cycles. Worth fixing on its own merits.

The trace that produced this answer has been removed; re-add it in one line if
needed (`print` the message length on entry to `backend_aot_write_diagnostic`).

## 2026-09-13, final state of this session

`llc not found` is the confirmed failure (13-byte diagnostic, traced). Two
attempts to fix it did NOT change the symptom, and both are landed because each
closed a real gap regardless:

1. **`PATH` added to the Stage 2 allowlist.** A genuine hole — the allowlist is
   the child's whole environment — but `bootstrap_stage_sanity` already exports
   `${stage_build_path}`, so the smoke likely had a PATH already.
2. **`SIMPLE_LLVM_BIN` / `LLVM_SYS_180_PREFIX` added to the allowlist.** The
   backend's finder consults these BEFORE any PATH lookup (`_env_tool_dirs`), and
   the MSVC lane exports the prefix. Symptom unchanged.

### The lead I would take next

`LLVM_SYS_180_PREFIX` is set to an **MSYS-style** path:
`/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc`. `_env_tool_dirs`
appends `/bin` and hands that to `file_exists`, from a process that is a NATIVE
Windows binary. Whether `/c/...` survives depends on `host_path_native`'s
`_mingw_drive_to_windows` running on that path. If it does not, the directory
probe fails, the finder falls through to `where llc`, and the result is
identical to having no configuration at all — which is exactly what we observe.

Cheapest decisive test: set `SIMPLE_LLVM_BIN` to a **native** path
(`C:/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin`) in the lane and
re-run. If that clears it, the defect is MSYS-vs-native path form in
`_env_tool_dirs`, not the allowlist at all.

### Re-tracing

The trace that named this was one line in `backend_aot_write_diagnostic`
printing `message.len()`. It was removed to keep `main` clean. Re-add it before
the next attempt — without it, every one of these runs is indistinguishable.

### Honest note on effort

This single defect consumed many bootstrap cycles in one session. Each cycle is
~40 minutes and the reason string is the ONLY signal, so guessing is expensive
and measuring is cheap. The trace answered in one run what four rounds of
inference could not. Start there.
