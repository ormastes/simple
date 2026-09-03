# Windows native-build: every produced binary calls `main` at the image base (0xC0000005)

- **Status:** OPEN
- **Filed:** 2026-09-01
- **Lane:** `x86_64-pc-windows-msvc`, LLVM backend, pure-Simple `native-build`
- **Severity:** blocker — no natively built Windows binary runs at all

## Symptom

`native-build` exits **0**, prints `Build complete: 1 compiled, 0 cached, 0 failed`
and `Linked: hello.exe (2383 KB) via clang-cl`, reports **zero** unresolved or
undefined symbols — and the binary it produced dies immediately:

```
$ ./hello.exe            # fn main(): print "hello from simple"
Segmentation fault (139)
$ ./empty.exe            # fn main(): val x = 1   -- no I/O at all
Segmentation fault (139)
$ powershell -c "... Start-Process ... ; '{0:X8}' -f $p.ExitCode"
C0000005                 # EXCEPTION_ACCESS_VIOLATION
```

An **empty** `main` crashes identically, so the fault is before any user
statement executes. The `--runtime-bundle core-c-bootstrap` composition crashes
the same way as the default one, so it is not a runtime-bundle selection issue.

## Measured root cause

`cdb` on the crash:

```
(3b78.2ca4): Access violation - code c0000005 (!!! second chance !!!)
00007ff7`7cd80000 4d5a            pop     r10        <-- executing "MZ"
  00007ff7`7ce20040 : ... : empty2+0xa0040
  00007ffa`b7d1ccb7 : ... : KERNEL32!BaseThreadInitThunk+0x17
```

The instruction pointer is the **module base** — the process is executing the
`MZ` bytes of the PE DOS header. Disassembling the caller
(`llvm-objdump -d --start-address=0x1400a0010`, preferred base `0x140000000`):

```
1400a001e: e8 3b 03 00 00   callq  0x1400a035e     ; _get_initial_narrow_environment
1400a0026: e8 39 03 00 00   callq  0x1400a0364     ; __p___argv
1400a002e: e8 25 03 00 00   callq  0x1400a0358     ; __p___argc
1400a0033: 4c 8b c7         movq   %rdi, %r8       ; envp
1400a0036: 48 8b d3         movq   %rbx, %rdx      ; argv
1400a0039: 8b 08            movl   (%rax), %ecx    ; argc
1400a003b: e8 c0 ff f5 ff   callq  0x140000000     ; <-- main, at RVA 0
1400a0040: 8b d8            movl   %eax, %ebx
```

This is the MSVC CRT's `invoke_main`. Its call to `main` is a direct `rel32`
whose target resolves to `0x140000000` — the image base, i.e. **RVA 0**.
Section table confirms `.text` starts at `0x140001000`, so RVA 0 is the PE
header, not code.

So: **`main` was linked to address zero and the link reported no error.** The
entry shim in
`src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl:138`
does emit `int main(int argc, char** argv)`, so either that object is not
reaching the link line or its `main` is being resolved to a null/absolute
symbol instead of the definition.

This is the Windows instance of the tolerated-undefined-symbol -> null-call
class already recorded in
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`, except the
symbol involved is `main` itself, and `check-no-unresolved-runtime-symbols.shs`
does not cover it (it scans `rt_*`-prefixed runtime symbols).

## Reproduction

```sh
. scripts/setup/windows-msvc-bootstrap-env.shs
printf 'fn main():\n    val x = 1\n' > empty.spl
SIMPLE_WINDOWS_ABI=msvc SIMPLE_LINKER_FLAVOR=msvc \
  <stage2>/simple.exe native-build --target x86_64-pc-windows-msvc \
  --backend llvm --entry empty.spl -o empty.exe   # exits 0
./empty.exe                                        # 0xC0000005
```

## Secondary defect found in the same investigation

The `--stop-after-stage2` failure path reported
`UNDIAGNOSABLE: the stage failed with no error message of any kind` while
citing `stage2-native-build.log` (81,573 bytes). The actual diagnostics were in
the sibling `stage2-receiver.log` (86,411 bytes) all along, and named two real
errors (C2040 on `rt_mmap`, C1189 on `<stdatomic.h>`). A diagnosable failure was
reported as undiagnosable purely because the wrong log was inspected. Fifth
member of the diagnostic-routing family.

## Next steps

1. Dump the actual link command line (add a level-gated trace in
   `llvm_native_link_orchestrator.spl`) and confirm whether
   `simple_entry{ext}` is on it.
2. If it is, inspect that object with `llvm-nm` for the storage class of
   `main`.
3. Add a link-time gate that fails when any *direct* call relocation in the
   produced image targets RVA 0 — that check is cheap, platform-neutral, and
   would have caught both this and the 2026-08-18 incident.

## Additional evidence (same session)

The entry shim's `main` is **absent from the linked image**, not merely
mis-addressed. `llvm-objdump -d` over the whole binary (139,693 instructions)
contains **no `$0x7d` immediate anywhere**, yet the shim's `main` unavoidably
materialises one: `if (__simple_startup_before_main(argc, argv) != 0) return 125;`
(`llvm_native_link_hosted_support.spl:143`). So `simple_entry{ext}` never
reached the link line, or was dropped from it, and the MSVC link nevertheless
succeeded with `main` bound to RVA 0 and emitted no LNK2019. No `/FORCE`,
`/FORCE:UNRESOLVED` or `--unresolved-symbols` flag appears anywhere in
`src/compiler/70.backend/backend/*.spl`, so the tolerance is coming from
somewhere else and is itself part of the defect.

`SIMPLE_COMPILER_TRACE=1` produced **no** `[LLVM-LINK]` / `[RT-COMPILE]` lines
from the stage-2 binary over an 851-line build log, so the level-gated link
trace that would show the link line is not reaching stdout on this lane — a
sixth diagnostic-routing gap, and the reason step 1 below is still open.

## Why this gates Stage 2 admission

`scripts/check/check-bootstrap-stage2-struct-receiver.shs:174` does not merely
link the route-guard binary — it **executes** it and compares stdout:

```sh
stage2_route_output=$($stage2_route_bin 2>&1)
stage2_route_expected=$(printf 'app.cli.bootstrap_main\ncompiler.driver.driver\napp.cli.main')
```

So a Stage-2 candidate cannot be admitted on Windows while every binary its
in-process pure-Simple driver produces dies at RVA 0. Admission is blocked on
this bug, not merely on the C-runtime compile failures fixed alongside it.
