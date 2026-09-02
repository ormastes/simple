# Aliased import is silently rebound to a same-named LOCAL function under native/AOT codegen

- **Filed:** 2026-09-03
- **Severity:** critical — produces a silent infinite self-recursion (stack overflow) in the emitted binary
- **Status:** OPEN
- **Platforms:** ALL. Reproduced on Windows MSVC; the defect is in the shared Rust-seed AOT lowering,
  not in any Windows-specific code. Linux/macOS bootstrap lanes are affected identically and are
  latent only because they have not rebuilt since 2026-09-02.

## Summary

`use M.{f as g}` followed by a call to `g()` inside a file that ALSO defines its own `fn f()`
is lowered, under `native-build` (AOT), to a call to the **local** `f` instead of `M::f`.
When the local `f` is the caller, the result is an unconditional self-call — LLVM turns the
tail self-call into `jmp self` and the process dies with a stack overflow.

The **interpreter is correct**; only the AOT path mis-binds.

## Minimal reproduction (6 lines, ~2 s)

```
# other.spl
pub fn probe() -> text:
    "OTHER"

# main.spl
use other.{probe as aliased_probe}

fn probe() -> text:
    aliased_probe()

fn main():
    print(probe())
```

```
A=build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe
$A run main.spl                     # => "OTHER"   (interpreter: CORRECT)
$A native-build --backend llvm ... -o main.exe main.spl
objdump -d -r <native-objects-*>/mod_0.o
```

Emitted object (measured):

```
0000000000000000 <..._fx__main__probe>:
   0:  eb fe    jmp    0 <..._fx__main__probe>      <-- infinite self-loop
```

**Zero relocation to `..._fx__other__probe`.** The alias target is lost.

**Negative control:** renaming the local `probe` to `probe_local` (no bare-name collision)
resolves correctly and emits `IMAGE_REL_AMD64_REL32 ..._fx__other__probe`.

**Scope matrix** (all four measured):

| `SIMPLE_BOOTSTRAP` | fixture | result |
|---|---|---|
| `1` | collision | `jmp self` — BUG |
| `1` | no collision | correct reloc |
| `0` | collision | `jmp self` — BUG |
| `0` | no collision | correct reloc |

So this is **not** bootstrap-flat-lowering specific: it is the whole AOT/native codegen path.

## How it bit the Windows MSVC Stage 2 bootstrap

Stage 2 candidate `build/bootstrap/stage2-rejected/x86_64-pc-windows-msvc/simple.exe`
(108,429,824 bytes, 2026-09-02 21:29) exits **127** on a two-line hello world, with the phase
trail ending at `aot:lower_to_mir:start` and no `:done`.

`127` is a red herring. Measured under `cdb`:

```
(25a8.6570): Stack overflow - code c00000fd (!!! second chance !!!)
simple+0x9a6ac0  push rsi / sub rsp,20h
simple+0x9a6ac5  e8 f6 ff ff ff   call simple+0x9a6ac0     <-- calls ITSELF
```

~36 identical frames at the same return address; all argument slots zero.
MSYS bash reports the abnormal termination as 127.

The recursing function is `host_os()` (`src/lib/nogc_sync_mut/platform.spl:46`) — identified from
the literal pool it references (`"windows"` at the compare, `"uname -s"`, then
`Linux/linux/Darwin/macos/FreeBSD/freebsd/OpenBSD/openbsd/NetBSD/netbsd`) and the
`/bin/sh` + `-c` helper it tail-calls.

The cycle, created by the 2026-09-02 FAIL-OPEN delegation fix:

```
platform.spl:21   use std.nogc_sync_mut.env.platform.{is_windows as platform_is_windows}
platform.spl:42   fn is_windows_env() -> bool: platform_is_windows()
platform.spl:46   pub fn host_os() -> text:
                      if is_windows_env(): "windows" else: <uname -s>
platform.spl:100  pub fn is_windows() -> bool: host_os() == "windows"    <-- LOCAL, same bare name
```

`platform_is_windows` should bind to `env/platform.spl:182 is_windows`. It is instead bound to
the local `platform.spl:100 is_windows`, closing the loop
`host_os -> is_windows_env -> is_windows -> host_os`. LLVM inlines the two one-line bool
wrappers, leaving exactly the disassembly above.

`src/lib/nogc_sync_mut/platform/__init__.spl` carries a byte-identical second copy of the same
cycle (`get_host_os -> is_windows_env -> platform_is_windows -> is_windows:72 -> get_host_os`).

## Unblock condition

Either:
1. **Preferred — fix the resolver:** an aliased import must bind to its recorded target
   (module + original name) and must NOT be shadowed by a local definition sharing the
   original bare name. A duplicate bare-name registration should at minimum be a hard error
   rather than silent last-write-wins.
2. **Stopgap:** remove the bare-name collision in the two `platform` files. This unblocks the
   Windows Stage 2 bootstrap but leaves the compiler defect live for every other caller.

## Regression test

The 6-line fixture above, asserted at the OBJECT level (a relocation to the imported symbol must
be present) — not just by running it, since the failure mode is a stack overflow that a runner
may report as an opaque non-zero exit.
