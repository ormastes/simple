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

## 2026-09-13 session close: what is fixed, what remains

### Fixed and landed (each verified)

- **`llc not found`** — the real backend failure. `find_llc` consults
  `_env_tool_dirs` (SIMPLE_LLVM_BIN / LLVM_SYS_180_PREFIX) before any PATH
  lookup, but `bootstrap_stage_sanity` scrubs the environment and re-exports
  only a fixed set, so those two were stripped exactly where needed. Carried
  through the scrub. Measured before: `find_llc: env_dirs=0 resolved=[]`;
  after: `env_dirs=1 resolved=[C:/dev/install/clang+llvm-18.1.8-.../bin]`.
- **Four nil-vs-empty defects**, all of which converted a real fault into an
  invisible one: the secure-temp-dir guard (`== ""` misses nil), the provider
  diagnostic guard, the discarded `file_atomic_write` result, and
  `file_read_regular_no_follow_bounded` returning `Ok(<nil>)` on a failed read.
  That last one is why this defect read as "diagnostic file empty" for many
  cycles: the message WAS written, the READ failed, and the failure was
  laundered into an empty success that pointed suspicion at the writer.

### The current, honest frontier

The failure is now reported truthfully:

```
backend object-path status 1 (diagnostic unreadable:
  regular no-follow bounded file read returned nil: <path>)
AOT diagnostic wrote 29 bytes but is unreadable
```

So the backend produces a 29-byte reason that still cannot be read back. The
write reports success; the read returns nil. Both go through `host_path_native`,
and host detection and separator normalisation are confirmed working
(`host_is_windows_host=true`).

### Methodology traps that cost real time here — read before continuing

1. **`src/runtime/*.c` is COMPILED INTO the binary; `src/lib/**` is read as
   source.** A probe run with the deployed `bin/simple.exe` (dated 2026-09-02)
   exercises the OLD C runtime and says nothing about a runtime change. Only a
   bootstrap run, or a locally rebuilt seed, tests those.
2. **Backslashes do not survive into heredocs reliably here.** Three separate
   probes and two C edits were corrupted by `\` collapsing to `\`, once
   silently turning `C:\Users\...` into escape sequences and producing a
   completely bogus "mixed separators fail" conclusion. Build path separators
   from a numeric code point, or avoid literals entirely by obtaining paths from
   the runtime (e.g. `secure_temp_dir`).
3. **`timeout` is not available under `env -i`.** Two readings of `rc=127`/`rc=1`
   were `timeout` failing, not the program under test. Read stderr.

### Next step

Instrument `rt_file_read_regular_no_follow_bounded` on the Windows branch the
same way `rt_secure_temp_dir` was instrumented (report `GetLastError` and the
path), then run ONE bootstrap. The reason string is the only signal a cycle
produces, and a one-line trace has out-performed every round of inference in
this investigation.

## 2026-09-13 — the read was never the fault (measured, not inferred)

`rt_file_read_regular_no_follow_bounded` now records which of its eleven exits
it took, in an atomic read back through
`rt_file_read_regular_no_follow_last_failure` and named in the Simple `Err`
text. The atomic starts at a sentinel (77) and stores a distinct value on
success (100), so a readout separates four states that all used to read as
zero: never called, succeeded, a named rejection arm, and "this diagnostic
extern is itself unresolved in the lane that read it".

Stage 2 sanity now reports:

    backend object-path status 1 (diagnostic unreadable:
    regular no-follow bounded file read returned nil (read succeeded): <path>)

**The reader ran and returned a real 29-byte heap string.** The nil is created
after the extern returns, between the `RuntimeValue` and the Simple `text?`
binding: `content.?` is TRUE (so the Optional is present and non-NIL) while
`content.unwrap().len()` is -1 (so the word inside does not decode as a heap
string). This is the force-unwrap Option-wrapper family, not file I/O.

### Hypotheses this retires, each with the measurement that killed it

- **MAX_PATH / extended-length paths.** `LongPathsEnabled` is `0x1` on this
  host and Rust's std already applies `maybe_verbatim`. A write+read probe at
  the exact failing path (267 chars) through the seed returns `write true /
  read ok len 26`. The Rust-side `long_path` helper written for this was
  reverted as dead code; the C-side widening in `runtime_native.c` and
  `runtime.c` is correct but was never on this path.
- **Mixed separators under a verbatim prefix.** Reproduced with the exact
  backslash/forward-slash mix from the log: still `read ok`. Both C helpers
  (`rt_widen_long_path`, `rt_secure_create_directory_long`) normalise `/` to
  the separator before `GetFullPathNameW` anyway.
- **The capability sandbox.** The gate is symmetric across read and write and
  returns true with no active sandbox; the write in the same process succeeded.
- **A C/Rust split of the reader.** Measured per archive: the C
  `runtime_sffi_c.lib` defines `rt_secure_temp_dir` and **not** the reader;
  `simple_native_all.lib` carries both. Staging is C, the reader is Rust, and
  they share one archive — no split-representation problem.
- **The `file_read_regular_no_follow_bounded` name collision.** Real (two
  co-compiled definitions, `(i64,i64,i64)->i64` in `sffi/fs.spl` vs
  `(text,i64)->Result<text,text>` in `io/file_ops.spl`, and the raw one breaks
  its own file's `_raw`/`_unchecked` convention) but **not this defect**: the
  warning does not appear in `stage2-sanity.env.frontend-failure.log`. Worth
  fixing as the hygiene the compiler asks for, separately.

### Methodology trap this run added

`arm 0` was read as "the reader succeeded" when zero was simultaneously the
atomic's initial value, the success code, and what an unresolved extern returns.
Three states on one number is not a measurement. A diagnostic code space must
make "I was never set" distinguishable from every real answer before its
readout is worth anything.

## 2026-09-13 (later) — the readout is now trustworthy, and it still says "read succeeded"

The first diagnostic was a process-wide atomic. That is worthless here: the
bootstrap reads with 24 jobs in flight, so a concurrent successful read on
another thread overwrites the code before the failing caller reports it. It
was made thread-local in both runtimes (Rust `thread_local!` Cell, C
`__declspec(thread)`/`__thread`) precisely so its answer could be believed.

The answer did not change:

    AOT diagnostic wrote 29 bytes but is unreadable
      (regular no-follow bounded file read returned nil (read succeeded))

That line is emitted by `backend_aot_write_diagnostic` itself — the write and
the read-back are the same function, the same thread, microseconds apart — and
it occurs 4 times per failing run. So on one thread, uncontended:

- the reader reaches `rt_string_new(raw.as_ptr(), raw.len())` and returns,
- the Simple `text?` is PRESENT (`content.?` is true, so the word is not NIL),
- and the word inside does not decode as a heap string (`.len()` is -1).

### What this does NOT support

A plain Optional-lowering bug. The exact driver shape — a real extern declared
`-> text?`, assigned into a declared `text?` slot, unwrapped, measured — was
run against the fresh seed in all three execution modes (default, interpreter,
jit) and returns the correct length every time. Three modules were NOT
rewritten to drop the Optional on the strength of a hypothesis this measurement
contradicts.

`Some(...)` into a declared slot IS corrupt on the deployed seed
(`var b: text? = nil; b = Some("hello")` gives `len -1`, while
`val a = Some("hello")` gives `len 5`) and IS fixed on the fresh seed, so that
is a real but separate defect and not this one.

### Where the remaining suspicion sits

Something between `rt_string_new` allocating and the caller decoding, that a
small single-purpose probe does not reproduce but a loaded 24-job compiler
does. Premature reclamation of an extern-allocated string, or a
mixed-vintage heap representation across the frozen `spl_hosted_runtime` rlib
and the freshly built runtime, both fit; neither is yet measured. Note that the
rlib's `-36e87d0608124df2` suffix is cargo's metadata hash and is stable across
content changes, so its constancy across rebuilds proves nothing either way —
an earlier reading of it as "not rebuilt" was wrong.

### Methodology note

Two diagnostics in a row were themselves defective before they were
informative: first a code space where 0 meant three different things, then a
global cell in a 24-thread program. Both produced confident, wrong readings.
An instrument has to be validated against the conditions it will be read
under, not just the conditions it was written under.
