# Guest clang/lld aarch64 binaries are mis-linked: crt0 drops argc/argv, weak `main` falls into `pread`, init pointers reference 0xb1c8 (outside all PT_LOADs)

Date: 2026-09-26
Lane: lane-C1 aarch64 in-guest clang compile (scripts/qemu/check_simpleos_arm64_clang_compile.shs)
Owner: guest toolchain lane (/home/yoon/llvm-project-simpleos, OUTSIDE this repo)
Found by: agent-30, Wall 10 ring-3 bring-up (route B lane-local handoff)

## Summary

The two guest payload binaries staged by the gate,
`cross-aarch64-unknown-simpleos/bin/clang-20` and `.../bin/lld`, cannot run
their own `main`. Three independent link defects, all external to this repo,
stop the clang/lld driver from ever executing. The kernel-side ring-3 handoff
(route B, this session) is proven working up to the guest's own first
instruction; R3 (`rung=R3-clang-version rc=0` + version banner) is blocked by
these binary defects, not by the kernel.

## Defect 1: stale crt0 — `_start` calls `main(0, 0, 0)`

The linked crt0 in both binaries zeroes BSS, calls `__libc_init_array`, then
`mov x0/x1/x2 = 0; bl main` — it never reads the SysV process-entry stack
frame the kernel builds (`sp[0]=argc, sp[1..]=argv`). The current libc source
`libc-build-x86_64/src/simpleos_crt0_aarch64.S` DOES read the frame
(`ldr x19, [sp]` …), so the crt0 objects in
`sysroot-aarch64/lib/crt0.o` / `libc-build-aarch64/simpleos_crt0.o` predate
that source. argv/envp can never reach the program.

clang-20 `_start` @ 0x10000000:
```
10000024: bl 1447a4c0 <__libc_init_array>
10000028: mov x0, #0x0
1000002c: mov x1, #0x0
10000030: mov x2, #0x0
10000034: bl 1447a020 <main>
10000038: bl 14480f28 <exit>
```

## Defect 2: weak `main` is a 4-byte fallthrough into `pread`

`main` is a WEAK symbol, 4 bytes, immediately before `pread`:

```
000000001447a020 0000000000000004 W main
000000001447a024 000000000000008c T pread
1447a020: 14000001  b 1447a024 <pread>   ; falls through into pread's body
```

The real driver entry `_Z4mainiPPc` (0x1000df1c) is never referenced by the
crt0's `bl main`. The x86_64 cross binary has the same weak-`main` shape
(`0000000014a93564 0000000000000005 W main`) but a separate body, so the
x86 lane's clang ran; the aarch64 link resolves `main` to the `pread`-adjacent
stub. Net effect: the process runs `pread(0, NULL, 0, 0)` and `exit(ret)`
instead of the clang driver — no version banner can ever print.

## Defect 3: `__libc_init_array` data pointers live at 0xb1c8/0xb1d0/0xb1d8 (no PT_LOAD covers them)

`__libc_init_array` (0x1447a4c0) reads its guard and its init_array bounds
through `adrp …, 0xb000` — a link-time constant pointing at page 0xb:

```
1447a4c8: adrp x8, b000
1447a4d0: ldr  x8, [x8, #456]     ; [0xb1c8] -> data abort (translation fault)
1447a520: adrp x19, b000
1447a528: ldr  x19, [x19, #464]   ; [0xb1d0] = __init_array_start ?
1447a52c: ldr  x9, [x9, #472]     ; [0xb1d8] = __init_array_end ?
```

The image is linked at 0x10000000 and `sysroot-aarch64/share/simpleos/simpleos.ld`
has no section at 0xb000, so 0xb1c8 is outside every PT_LOAD. First in-guest
execution therefore data-aborts at ELR 0x1447a4d0, FAR 0xb1c8,
ESR 0x92000006/0x92000007 (translation fault).

## In-guest evidence (run-20260926_002603)

With the kernel's ring-3 handoff working (validate -> 20,948 pages mapped ->
SysV stack -> eret), the guest:

```
[payload] eret to EL0
FAULT @ 0x000000001447a4d0  ESR=0x92000006  FAR=0x000000000000b1c8
```

After the kernel mapped the low 16 pages zeroed (a DIAGNOSTIC workaround, not
a fix — the reads return 0 and the cbz skips the guard load), the guest
completed the full EL0 round trip:

```
[payload] eret to EL0
[arm64-user] svc exit; resume kernel
[payload] payload exited code=-1
[clang-bringup] rung=R3-clang-version rc=-1
```

rc=-1 is `pread`'s return (its `lseek(0,…)` SVCs return -38/ENOENT-class
errors): the payload genuinely executed in EL0, made syscalls, and exited
through the kernel resume frame. This proves the kernel-side ring-3 machinery
end to end; it cannot produce a banner or rc=0 while the binary's main never
runs the driver.

## Required toolchain fixes (owner: guest toolchain lane)

1. Rebuild `sysroot-aarch64/lib/crt0.o` (and `libc-build-aarch64/simpleos_crt0.o`)
   from the current `simpleos_crt0_aarch64.S` so `_start` reads the
   process-entry stack frame and passes argc/argv/envp to main.
2. Fix the guest link so `main` resolves to the clang/lld driver main
   (`_Z4mainiPPc` / a correct `main` shim), not the weak `pread`-adjacent stub.
3. Fix the mis-relocation that places `__libc_init_array`'s guard/init_array
   bounds at 0xb1c8/0xb1d0/0xb1d8; they must be ordinary image symbols inside
   a PT_LOAD.

Until all three land, R3-R5 of the aarch64 in-guest clang gate stay red for
reasons external to this repository.
