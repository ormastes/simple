# Windows MSVC Stage 2: struct-receiver capability probe SEGVs (new, distinct from the resolved module-init bug)

- **Date:** 2026-09-01
- **Status:** OPEN — root cause not yet investigated. Reproduced by hand,
  isolated to a specific gate, and shown to be a DIFFERENT defect than the
  already-RESOLVED module-init SEGV
  (`windows_msvc_module_init_alternatename_link_order_2026-08-31.md`).

## Symptom

On branch `work/windows-bootstrap-msvc-rebased`, once the Stage 2 sanity gate
was fixed to actually exercise the MSVC/clang-cl lane (see the three fixes
below), the bootstrap's NEXT gate — `check-bootstrap-stage2-struct-receiver.shs`
— fails. It builds `test/04_smoke/bootstrap_struct_receiver_guard.spl` with
the freshly-built (sanity-passed) Stage 2 binary acting as the compiler, then
runs the result:

```
Build complete: 1 compiled, 0 cached, 0 failed
  Binary: .../bootstrap-struct-receiver-guard (0 KB)
  Time: 0.1s compile + 5.8s link = 5.9s total
error: stage2 receiver probe failed with status 139
```

Reproduced by hand (matching the bootstrap's exact env: `vcenv5.txt`
INCLUDE/LIB/LIBPATH, LLVM 18.1.8 + MSVC 14.44.35207 on PATH,
`SIMPLE_WINDOWS_ABI=msvc`, `SIMPLE_LINKER_FLAVOR=msvc`, `SIMPLE_BOOTSTRAP=1`):

```
$ ./probe.exe
Segmentation fault      rc=139
```

## The "(0 KB)" binary-size line is a display artifact, not the bug

The build-log formatter prints `(0 KB)` for the output binary regardless of
its real size — `ls -la` on the actual reproduced artifact shows
**2,440,704 bytes**, a normal-sized native PE, not an empty/degenerate file.
Ruled out as a lead; not investigated further here (a formatter rounding/unit
bug, separate and cosmetic).

## Why this is NOT the already-resolved module-init bug

`windows_msvc_module_init_alternatename_link_order_2026-08-31.md` tracked (and
its fix commits `a833758eb18`/`88ec90eb472` resolved) a SEGV in a **2-line
hello-world** `compile`, caused by the MSVC `wmain` stub never calling
`__simple_call_module_inits()`. Both fix commits are present on this branch
(`git merge-base --is-ancestor` confirms both are ancestors of HEAD), and that
doc's own end-to-end verification shows the 2-line-hello-world repro no longer
crashes.

This probe's fixture (`test/04_smoke/bootstrap_struct_receiver_guard.spl`) is
materially different: it exercises class instantiation with a mutable field
write, tuple field access, `text.len()`, and struct-value aggregate copy —
none of which the hello-world repro touches. The fix that resolved the
module-init bug is real and still in effect; this is new territory the
module-init fix's own verification never exercised.

## Path to reproduce

```bash
export LLVM_SYS_180_PREFIX="/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc"
export INCLUDE="$(grep -E '^INCLUDE=' /tmp/vcenv5.txt | head -1 | cut -d= -f2-)"
export LIB="$(grep -E '^LIB=' /tmp/vcenv5.txt | head -1 | cut -d= -f2-)"
export LIBPATH="$(grep -E '^LIBPATH=' /tmp/vcenv5.txt | head -1 | cut -d= -f2-)"
export PATH="$LLVM_SYS_180_PREFIX/bin:/c/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64:$PATH"
export SIMPLE_WINDOWS_ABI=msvc
export SIMPLE_LINKER_FLAVOR=msvc
B=build/w/stage2-rejected/x86_64-pc-windows-msvc/simple.exe   # the sanity-passed, receiver-rejected candidate
D=/tmp/recv_probe; rm -rf "$D"; mkdir -p "$D/cache"
env SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  "$B" native-build --target x86_64-pc-windows-msvc --backend llvm \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --threads 1 --cache-dir "$D/cache" \
  --entry test/04_smoke/bootstrap_struct_receiver_guard.spl \
  --runtime-path "$(pwd)/build/w/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority" \
  -o "$D/probe"
"$D/probe.exe"   # SIGSEGV, rc=139
```

## Suggested next steps (not yet attempted)

- Bisect which construct triggers it: reduce `bootstrap_struct_receiver_guard.spl`
  to just the class field write, then just the tuple access, then just
  `text.len()`, then just the struct copy, to isolate which one(s) crash.
- `cdb` (or equivalent) on the reproduced `probe.exe`, same technique used to
  diagnose the resolved module-init bug (disassemble at the fault, check
  whether the faulting address falls in the PE-loader-zeroed BSS tail — same
  signature as an uninitialized-global read — or is a genuinely different
  fault class, e.g. a bad vtable/class-layout pointer specific to MSVC ABI).
- Check whether `SIMPLE_BOOTSTRAP=1` (the exact mode this probe runs under,
  and the one Stage 3 uses) changes codegen in a way `SIMPLE_BOOTSTRAP=0` does
  not — the sanity gate's own comment (`candidate_frontend_smoke`,
  `CANDIDATE_FRONTEND_BOOTSTRAP`) already documents `SIMPLE_BOOTSTRAP=1`
  "changes compiler behaviour drastically" elsewhere in this codebase.

## Context: the chain of fixes that reached this gate

This bug was unreachable until four earlier, independently-real fixes landed
on this branch (`work/windows-bootstrap-msvc-rebased`), each masking the next:

1. `a927aac3dc3` — the sanity gate discarded its own frontend-smoke log on
   failure, so every failure surfaced as `frontend_status=1` with literally no
   error text ("UNDIAGNOSABLE"). Fixed by preserving the log durably.
2. `e7bd142da09` — `bootstrap_stage_sanity` scrubs the ENTIRE environment
   before running the candidate, then restored only
   `HOME`/`TMPDIR`/`PATH`/`LC_ALL`/`LANG`. On Windows this dropped
   `SIMPLE_WINDOWS_ABI`/`SIMPLE_LINKER_FLAVOR`, so `Target::linker_flavor()`
   fell back to an `MSYSTEM` heuristic (always set under Git Bash) and ran the
   GNU lane instead of the requested MSVC lane — exactly the
   `bootstrap_windows_abi_env` gap already documented at this file's line
   ~835 ("measured 2026-08-30: Failed to compile main stub (g++)") but never
   wired into the sanity check specifically. Fixed by forwarding
   `SIMPLE_WINDOWS_ABI`/`SIMPLE_LINKER_FLAVOR`/`INCLUDE`/`LIB`/`LIBPATH`/
   `SystemRoot`/`SystemDrive`/`ProgramData`/`TEMP`/`TMP` into the scrubbed env.
3. `a53e5c2f2ba` — with (2) fixed, the sanity smoke now genuinely ran MSVC and
   failed for real, but `candidate_frontend_smoke`'s own failure handler
   dumped `head -c 65536` of the build log — the FIRST 64 KB, dominated by
   compiler warnings from an unscoped `--entry-closure` project-wide scan, so
   the actual error at the end was never visible. Fixed by dumping the tail
   instead.
4. `8df1989a431` — with (3) fixed, the real error was: `LNK2019: unresolved
   external symbol __cpu_indicator_init`/`__cpu_model` referenced from
   `rt_simd_has_sse`. `__builtin_cpu_init`/`__builtin_cpu_supports`
   (`runtime_simd_dispatch.c`) need `clang_rt.builtins-<arch>.lib`, which nothing
   linked on the MSVC hosted lane (only the freestanding lane did). Fixed by
   linking it via `find_msvc_compiler_rt_builtins`.
5. `4ba6f6a7ca4` — with (4) fixed, the next error was `LNK2005: spl_thread_cpu_count
   already defined` — both `runtime_legacy_core.c` (always compiled) and
   `runtime_thread.c` (via a stale `_WIN32` exception) defined it. Fixed by
   restoring the single-owner guard.

With all five landed, the sanity gate now genuinely PASSES on Windows MSVC —
this document's bug is the next, previously-unreachable gate.

## Verified state at the time of filing

```
$ ls -la build/w/stage2/x86_64-pc-windows-msvc/
simple.exe.rejected          108219904 bytes, Sep  1 07:09  (STALE — from an earlier sanity-failure run)
simple.exe.rejected.prefix   108194816 bytes, Aug 31 16:43  (STALE)
# no bare `simple.exe` — sanity passed this run, so nothing was renamed here

$ ls -la build/w/stage2-rejected/x86_64-pc-windows-msvc/
simple.exe        108219904 bytes, Sep  1 07:44  (sanity-PASSED, receiver-REJECTED candidate)
rejection.env                 493 bytes, Sep  1 07:45  (reason=stage2-struct-receiver-failed)

# no build/w/stage2-admitted/ directory — admission was NOT reached.
```

## RESOLVED 2026-09-01 — root cause found, none of the four capabilities faults

Bisected the fixture into four single-capability `.spl` files (class field
write, tuple index, `text.len()`, struct-value copy) and a plain two-line
`print("hello"); return 0` control. **All five crash identically** (rc=139,
same faulting address) under the probe's exact `native-build` invocation.
This rules out every "which capability" theory from the earlier draft of
this doc — the fault is not in receiver/struct-copy codegen at all, and
fires before any user code runs.

### The fault, disassembled

`cdb -c "g; k; r; u; q"` on the reproduced binary shows the SEGV at
`rip = ImageBase + 0` (the loaded module's own DOS/PE header bytes,
`4d 5a` = "MZ", executed as code) with return address `probe+0xa0010`.
`llvm-objdump -d` on that return address resolves to:

```
1400a0003: 4c 8b c7        movq   %rdi, %r8      ; envp
1400a0006: 48 8b d3        movq   %rbx, %rdx     ; argv
1400a0009: 8b 08           movl   (%rax), %ecx   ; argc
1400a000b: e8 f0 ff f5 ff  callq  0x140000000    ; == ImageBase exactly
1400a0010: 8b d8           movl   %eax, %ebx      ; <- return address, matches cdb frame
```

Three-argument cdecl call `(argc, argv, envp)` from inside CRT startup
(`__scrt_common_main_seh`'s `invoke_main()`, ~0x80 bytes before
`AddressOfEntryPoint`) is the classic MSVC `wmain(argc, argv, envp)`
invocation. **The linker resolved the `wmain` call target to RVA 0** — a
direct E8 near call, so this was baked in at LINK time, not corrupted by a
missing base relocation at load time.

### Root cause: default clang-cl link path silently no-ops symbol resolution failures

`linker.rs`'s `link_objects` (~line 1811-1834), when
`SIMPLE_NO_STUB_FALLBACK` is *not* set (the default — and what the probe's
first `native-build` invocation used), appends to the clang-cl link line:

```
/WHOLEARCHIVE            (bare -- no `:lib` qualifier, forces every
                           input archive fully in)
/FORCE:MULTIPLE,UNRESOLVED
```

The code's own pre-existing comment already flagged the bare `/WHOLEARCHIVE`
as pulling in duplicate import descriptors ("Narrowing that is a linker-
contract change and is deliberately left for its own commit") but had not
been connected to a crash. Combined with `/FORCE:MULTIPLE,UNRESOLVED`
(which suppresses both LNK2005 duplicate-definition and LNK2019 unresolved-
external as hard errors), the MSVC linker picks a bogus resolution for the
generated `wmain` and emits it anyway — RVA 0 rather than the real function
in `_main_stub.o` — with **zero diagnostic output** (`build.log` for the
failing run has no `LNK4xxx`/`LNK2xxx` lines at all). Binary size is a
strong corroborating signal: 2,440,704 bytes with the default/broken path
vs **165,376 bytes** for the identical source built with
`SIMPLE_NO_STUB_FALLBACK=1` — a ~15x blowup from whole-archiving every
input, consistent with the pre-existing comment's prediction.

**Confirmed by A/B**: the exact `bootstrap_struct_receiver_guard.spl`
fixture, unchanged, run through the identical `native-build` command,
only with `SIMPLE_NO_STUB_FALLBACK=1` added:

```
build_rc=0
bootstrap struct receiver guard
run_rc=0
```

### Why the earlier "value-transport/ABI" prior (task item 3) is dead

Every one of the four capabilities, and even code that exercises none of
them, faults identically. This is not a struct-copy, tuple-access, or
receiver-ABI defect. It is a link-time symbol-resolution failure that
happens to manifest as a crash during the CRT's call into user `wmain`,
before `spl_main`/`main` — and therefore before struct receivers,
tuples, text methods, or aggregate copies are ever reached.

### Fix

`scripts/check/check-bootstrap-stage2-struct-receiver.shs`'s first probe
(the one that builds and runs this fixture) was missing
`SIMPLE_NO_STUB_FALLBACK=1` on the MSVC lane — the *second* probe further
down the same file (the positional Stage-3 route check) already carries it
unconditionally, for this exact reason, and was not affected. Fixed by
setting it, scoped to `*windows-msvc*` targets only so the Linux/macOS
lanes this same script also runs under are byte-for-byte unaffected
(verified only on Windows here; commits `64b50bb5d61`, `0cb65d3078f`).

### Unix impact

None expected, and the scoping makes this provable rather than assumed:
the added `case "$stage2_target" in *windows-msvc*)` guard means
`SIMPLE_NO_STUB_FALLBACK` resolves to the empty string (== unset, per the
Rust side's `Ok("1")` check) on every non-MSVC target, so Linux/macOS
invocations of this script take a byte-identical code path to before.
The underlying `linker.rs` defect (bare `/WHOLEARCHIVE` +
`/FORCE:MULTIPLE,UNRESOLVED` silently no-oping real link errors) is not
Windows-specific in principle -- the same code path exists for other
`is_clang_cl`/`is_msvc` targets -- but was not touched or re-tested here;
narrowing that flag pair generally is the still-open, deliberately
deferred linker-contract change the pre-existing comment in `linker.rs`
already calls out.

### Remaining work

The struct-receiver gate itself now passes
(`bootstrap_stage2_struct_receiver=PASS`, measured by hand). The *second*
probe in the same script (positional Stage-3 route) then failed with
`Error: --threads requires a positive integer` (worker `native-build`
invocation, exit code 2) — a distinct, pre-existing issue unrelated to
this bug and not touched by this fix. Full stage2 admission is still
blocked on that. Not investigated further here; needs its own bug record
if it reproduces on a clean end-to-end run.
