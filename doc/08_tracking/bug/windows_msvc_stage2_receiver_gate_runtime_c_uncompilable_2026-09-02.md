# Windows MSVC: Stage 2 admission blocked — cl.exe cannot compile runtime.c

- **Date:** 2026-09-02
- **Status:** PARTIALLY FIXED (2026-09-06) — C sources now compile under cl.exe;
  the compiler-flag half is still open in the Rust runtime-compile path.
  Stage 2 admission NOT observed from this lane.
- **Failing gate:** `Stage 2: proving struct receiver/runtime capability`
  (`scripts/bootstrap/bootstrap-from-scratch.sh:2592-2626`, exit 3)
- **Lane:** `x86_64-pc-windows-msvc`, worktree pinned at
  `6e9660e36719c9775c742b7e7c331c8b55068184`

## What happened

Stage 2 **built and linked cleanly** — `819 compiled, 0 cached, 0 failed`,
`Linked: simple.exe (105677 KB) via clang-cl`, 676.7s compile + 38.3s link.

It then FAILED the post-build receiver capability probe
(`scripts/check/check-bootstrap-stage2-struct-receiver.shs`) and the wrapper
correctly quarantined the artifact rather than publish it:

```
build/bootstrap/stage2-rejected/x86_64-pc-windows-msvc/rejection.env
  schema=simple-bootstrap-rejected-stage2-v1
  status=rejected
  reason=stage2-struct-receiver-failed
  candidate_sha256=0bb90d16a57f3773edba3ec3d61728bb4c0522ab1fee582df89b6a1a1ca132d0
```

`stage2-receiver.env`: `status=fail`, `probe_exit=1`. The binary hash is
IDENTICAL before and after the probe, so the candidate is not self-mutating;
only the probe failed.

## Root cause

The probe asks the freshly built Stage 2 compiler to native-build a fixture. It
gets through source_closure, parse, HIR, monomorphize, LLVM IR and `llc`, then
fails when it compiles the C runtime for the link:

```
error: Bootstrap LLVM link failed (...): Runtime compilation failed:
Failed to compile runtime.c:
platform_win.h(276): warning C4028 (x2), C4029
platform_win.h(457): error C2040: 'rt_mmap':
  'int64_t (const uint8_t *,uint64_t,int64_t,int64_t,int64_t)' differs in
  levels of indirection from 'void *(const char *,int64_t,int64_t,int64_t)'
platform_win.h(492,498,509): warning C4028
vcruntime_c11_stdatomic.h(16): fatal error C1189: "C atomics require C11 or later"
Microsoft (R) C/C++ Optimizing Compiler Version 19.44.35228 (x64)
```

(MSVC emits these in the host locale — Korean on this box. The bootstrap's own
diagnostic matcher recognised none of it and reported
`UNDIAGNOSABLE: the stage failed with no error message of any kind`, which is a
second, separate defect: the real cause was in the log the whole time.)

Two independent defects, both Windows-only:

**1. `rt_mmap` signature divergence.** The Windows definition does not match the
prototype; the Unix one does:

| site | signature |
|---|---|
| `src/runtime/runtime.h:250` (prototype) | `void* rt_mmap(const char* path, int64_t size, int64_t offset, int64_t readonly)` |
| `src/runtime/platform/unix_common.h:304` | `void* rt_mmap(const char* path, int64_t size, int64_t offset, int64_t readonly)` — MATCHES |
| `src/runtime/platform/platform_win.h:457` | `int64_t rt_mmap(const uint8_t* path_ptr, uint64_t path_len, int64_t size, int64_t offset, int64_t readonly)` — DIVERGES |

`platform_win.h:457`'s own comment claims the `(ptr, len)` form is "per
runtime.h", but `runtime.h:250` says otherwise. The C4028/C4029 warnings at
lines 276, 492, 498 and 509 show this is a FAMILY of divergences, not one
function.

**2. No `/std:c11` on the runtime-compile path.** `runtime.c` uses C11 atomics;
`cl.exe` without `/std:c11` rejects `<vcruntime_c11_stdatomic.h>` outright.

## Why it was masked until now

The OUTER Stage 2 link uses **clang-cl**, which is permissive about both (it
defaults to a C standard with atomics). The compiler's own embedded
runtime-compile path invokes **cl.exe** instead, where both become fatal. So a
green Stage 2 build is not evidence the runtime compiles.

## Unblock condition

1. **Fix `runtime.h:250`, NOT `platform_win.h`** (direction verified against the
   caller — see "Which side is canonical" below). The C4028 sites at
   276/492/498/509 are warnings, not part of the minimal unblock: file, do not
   fix them in the same change.
2. Add `/std:c11` (or route this path to clang-cl, matching the outer link) to
   the runtime-compile invocation.
3. Re-run the receiver probe; Stage 2 admission should then proceed.

Separately: teach the bootstrap diagnostic matcher to recognise MSVC error
codes (`error C\d+`, `fatal error C\d+`) so a locale-translated failure is never
again reported as UNDIAGNOSABLE.

## Cross-platform impact

None on Unix. `unix_common.h` already matches the prototype and is untouched by
the proposed change; `/std:c11` applies only to the MSVC invocation.

## Which side is canonical — the caller decides (verified 2026-09-02)

An earlier draft of this record proposed reconciling `platform_win.h` TO
`runtime.h`. **That direction is wrong** and would have compiled clean while
breaking at runtime. C2040 proves the two sides disagree; it does not say which
is right. The caller does:

```
src/lib/nogc_sync_mut/io/file_ops.spl:24
  extern fn rt_mmap(path: text, size: i64, offset: i64, readonly: i64) -> i64
src/lib/nogc_sync_mut/io/file_ops.spl:250
  rt_mmap(path, size, offset, if readonly: 1 else: 0)
```

The extern returns **i64**, not `void*`, and its `path: text` parameter lowers
to the **(ptr, len)** pair. That is exactly `platform_win.h:457`'s
`int64_t rt_mmap(const uint8_t*, uint64_t, int64_t, int64_t, int64_t)`.

So `platform_win.h` is CORRECT and its comment is accurate; the stale side is
the `runtime.h:250` prototype (and, on its own terms,
`unix_common.h:304`, which still has the old `void*`/`const char*` form).

**Do not simply rewrite `runtime.h:250` globally** — that would make
`unix_common.h` mismatch and break the Unix build. Whoever picks this up must
first establish how the `text` extern is marshalled on Unix (whether Unix is
latently wrong here but never exercised on the bootstrap path). The
lowest-risk unblock for the Windows lane alone is a `#ifdef _WIN32` prototype
in `runtime.h` matching `platform_win.h`, leaving every Unix declaration and
definition byte-identical.

## Not mid-lane skew — present at the newer sha too

Checked against `b7b4ef8e060` (the later head of the same session lane): the
divergence is IDENTICAL there (`runtime.h:250` still `void*`/`const char*`,
`platform_win.h:457` still `(ptr,len)`/`int64_t`). This is a standing defect,
not a half-landed change, and building the newer sha would not avoid it.


---

## Re-measurement 2026-09-06 (lane E, real Windows 11 box, cl.exe 19.44.35228 x64)

Re-measured against the current tree, not the record's text. **Defect 1 is
STALE — already fixed upstream.** All three sites now agree on the tagged-value
form and no C2040 is emitted:

| site | current signature |
|---|---|
| `src/runtime/runtime.h:262` | `int64_t rt_mmap(int64_t path_value, int64_t size, int64_t offset, int64_t readonly)` |
| `src/runtime/platform/platform_win.h:457` | identical |
| `src/runtime/platform/unix_common.h:309` | identical |

**Defect 2 is real, and was larger than recorded.** `/std:c11` alone is not
enough — MSVC 19.44 then says `fatal error C1189: "C atomic support is not
enabled"` and needs `-experimental:c11atomics` as well. Underneath that gate sat
80 further errors in `runtime.c` and 73 in `runtime_native.c` that the C1189
had been hiding.

### Before (reproduced 2026-09-06)

```
$ cl.exe -c -nologo -I src/runtime src/runtime/runtime.c
vcruntime_c11_stdatomic.h(16): fatal error C1189: #error: "C atomics require C11 or later"

$ cl.exe -c -nologo -std:c11 src/runtime/runtime.c
vcruntime_c11_stdatomic.h(12): fatal error C1189: #error: "C atomic support is not enabled"

$ cl.exe -c -nologo -std:c11 -experimental:c11atomics src/runtime/runtime.c
runtime.c(108-111): error C2099: initializer is not a constant   [ATOMIC_VAR_INIT]
runtime.c(1576): error C2143/C2059/C2091/C2082 ...              [__attribute__((weak))]
  -> 80 errors total
$ ... src/runtime/runtime_native.c
  -> 73 errors total (__attribute__((weak)), __atomic_thread_fence, __asm__)
```

### Source-side fix (this change, `src/runtime/**` only)

- `runtime.h` — new `SPL_WEAK` macro: `__attribute__((weak))` everywhere except
  `_MSC_VER && !__clang__`, where it expands to nothing (MSVC has no weak
  symbols and no `__attribute__` syntax). Gated off `__clang__` deliberately so
  **clang-cl is byte-identical**, preserving the weak-external lowering the
  existing `SPL_CLI_ARGS_WEAK` note depends on. Linux/macOS/FreeBSD unchanged.
- `runtime.c` — 14 `__attribute__((weak))` -> `SPL_WEAK`; `ATOMIC_VAR_INIT(0)`
  -> `0` on the four probe counters (the macro is deprecated in C17 and removed
  in C23; plain init is valid C11 on clang/gcc, so no ifdef).
- `runtime_native.c` — 12 `__attribute__((weak))` -> `SPL_WEAK`;
  `__atomic_thread_fence(__ATOMIC_SEQ_CST)` -> `MemoryBarrier()` under MSVC;
  two `__asm__ volatile ("" ::: "memory")` compiler barriers ->
  `_ReadWriteBarrier()` under MSVC. All three are `#if defined(_MSC_VER) &&
  !defined(__clang__)` forks — genuinely irreducible, no portable C spelling.

### After

```
src/runtime/runtime.c        rc=0  errors=0
src/runtime/runtime_native.c rc=0  errors=0
   (cl.exe -c -nologo -std:c11 -experimental:c11atomics -I src/runtime)
```

`clang -fsyntax-only -I src/runtime src/runtime/runtime.c` -> exit 0 (only the
pre-existing `strdup` deprecation warning), so no Unix regression.

### Gate

`sh scripts/check/check-c-runtime-compiles-push.shs`:

```
FAIL — 5 file(s) failed to compile: src/runtime/test/rt_tls13_sha256_sleep_selfcheck.c
src/runtime/test/runtime_coverage_core_selfcheck.c
src/runtime/test/runtime_process_owned_adapter_selfcheck.c
src/runtime/test/runtime_time_failure_selfcheck.c
src/runtime/test/runtime_timestamp_failure_selfcheck.c
(105 compiled clean, 21 skipped for unavailable external dependencies)
```

**Byte-identical before and after this change** — same 5 offenders, same 105
clean. All five are POSIX-only selfchecks (`clockid_t`, `nanosleep`) failing on
a Windows host; none is a file this change touches. Not a regression; a
pre-existing Windows-host red for the gate.

### What remains open

1. ~~**The two flags are not wired.**~~ **WIRED 2026-09-06.** Corrected
   location: the invocation is **not** in `native_project/linker.rs` —
   `LinkerBuilder::compile_c_runtime` there is a dead stub returning
   `Ok(Vec::new())`. The live runtime-compile invocations are in
   `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`:
   `build_c_runtime_library` (core-C archive, the reachable Windows path),
   `build_sqlite_runtime_object`, and `build_stage4_cli_c_provider_archives`.
   All three now call a new helper `msvc_c11_atomics_flags(&cc)`, which appends
   `-std:c11 -experimental:c11atomics` **only** when the resolved compiler
   binary is cl.exe (`cc_detect::is_msvc_compiler`) or clang-cl. Gating is on
   the compiler binary, not `LinkerFlavor::Msvc`, because that flavor can also
   resolve to plain `clang` (see `MSVC_C_COMPILERS`), whose GNU driver rejects
   `-std:c11`; every gcc/clang lane on Linux/macOS gets an empty slice and an
   argument vector that is byte-identical to before.
   Measured 2026-09-06 on the real Windows box, through the driver's exact flag
   list (`-c -Os -ffunction-sections -fdata-sections -fno-unwind-tables
   -fno-asynchronous-unwind-tables -fno-stack-protector -fPIC -std=gnu11` +
   the two new flags + `-DSIMPLE_CORE_C_STANDALONE=1 -I src/runtime
   -I src/runtime/platform`):
   - `cl.exe` 19.44.35207: `runtime.c` **rc=0**, `runtime_native.c` **rc=0**,
     0 errors, 7 `warning D9002` (the GNU-shaped flags are ignored, not fatal).
     Without the two flags the same command dies at
     `fatal error C1189: "C atomics require C11 or later"`.
   - `clang-cl` 18.1.8: `runtime_native.c` **rc=0** both with and without the
     flags; `-experimental:c11atomics` is only reported as
     `argument unused during compilation`. Included in the gate so both MSVC
     drivers share one flag set.
   Note for the next lane: on this box `detect_c_compiler_for_target` resolves
   to **clang-cl** (it is on PATH), so cl.exe is used only when clang-cl is
   absent or `CC` names it. Also note `runtime.c` is **not** in the core-C
   `runtime_inputs` list — only `runtime_native.c` is — so its clean cl.exe
   compile above is direct evidence about the file, not about a driver step
   that compiles it.
   Unverified: no end-to-end Windows `native-build` was run through the changed
   code path (still blocked on Stage 2 admission, item 2 below).
2. **Stage 2 admission NOT observed.** This lane proved only that the two C
   translation units compile; it did not run
   `check-bootstrap-stage2-struct-receiver.shs` or reach admission.
3. Not attempted: the C4028/C4029 warning family at `platform_win.h`
   276/492/498/509 (warnings, explicitly out of the minimal unblock), the
   `-fsyntax-only`-can't-see-it link stage, and the bootstrap diagnostic
   matcher's blindness to `error C\d+` (still filed, still unfixed).
