# Windows MSVC: Stage 2 admission blocked — cl.exe cannot compile runtime.c

- **Date:** 2026-09-02
- **Status:** OPEN — blocks Phase 2 (Stage 2) admission, and therefore Phase 3
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

1. Reconcile the Windows runtime signatures with `src/runtime/runtime.h` (start
   with `rt_mmap`, then the C4028 sites at 276/492/498/509).
2. Add `/std:c11` (or route this path to clang-cl, matching the outer link) to
   the runtime-compile invocation.
3. Re-run the receiver probe; Stage 2 admission should then proceed.

Separately: teach the bootstrap diagnostic matcher to recognise MSVC error
codes (`error C\d+`, `fatal error C\d+`) so a locale-translated failure is never
again reported as UNDIAGNOSABLE.

## Cross-platform impact

None on Unix. `unix_common.h` already matches the prototype and is untouched by
the proposed change; `/std:c11` applies only to the MSVC invocation.
