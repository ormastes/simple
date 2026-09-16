# The SFFI facade cannot call a variadic libc function with a pointer — it SEGVs

Filed 2026-09-03. Status: OPEN.

## Symptom

`spl_wffi_call_i64` (the dynamic-SFFI call facade reached via
`spl_dlopen`/`spl_dlsym`) transmutes the resolved symbol to a **fixed,
non-variadic** function pointer — there is no libffi path. Calling a variadic
libc function that takes a pointer argument therefore passes it under the wrong
ABI. On Apple arm64 the callee reads the argument from the stack while the
caller passed it in a register.

Measured 2026-09-03: **every `ioctl(2)` call carrying a pointer SEGVs the host,
rc=139.**

## Concrete blocker it caused

A pure-Simple PTY twin could implement open / spawn / read / write / close /
is_alive against libc, all live-verified, but **`resize` is unimplementable**:
`TIOCSWINSZ` is only reachable through `ioctl`, which is variadic and takes a
`struct winsize*`. The function returns 0 (failure) unconditionally rather than
crashing the caller.

Alternatives ruled out by measurement, not assumption:
- `syscall(SYS_ioctl, ...)` through the same facade → `EBADF`.
- `tcsetwinsize` / `tcgetwinsize` → not exported by libSystem on this host.
- Initial window size *is* settable, because `openpty` takes the `winsize` up
  front as a normal (non-variadic) argument. Only *later* resizes are blocked.

## Scope

Any variadic-with-pointer libc call from Simple: `ioctl`, `fcntl` with a
pointer command, `open` with mode in some ABIs, `printf`-family. Non-variadic
calls and variadic calls with only integer arguments are unaffected.

## What "fixed" looks like

A stack-argument or libffi-backed path in `spl_wffi_call_i64` (or a sibling
entry point that declares the variadic boundary explicitly), so the caller can
state where the argument belongs. That single change unblocks the whole class.

## Related seed parse defects found in the same lane (minor, worked around)

- `export fn f(...) -> (text, i64):` fails with `expected identifier, found
  LParen`. A separate `export f` statement parses fine, so tuple-returning
  functions can be exported — just not inline.
- `export val X: i64 = -1` fails; `export val X = -1` "succeeds" but exports the
  **symbol** `:X` rather than the value. Silent, and the wrong shape.

Both were worked around rather than normalized silently, per the repo rule
against quietly accepting a workaround for a short, safe form that should work.

## Not claimed here

That the PTY twin should be revived. That lane was dropped for an unrelated and
better reason — a PTY stack already exists at `origin/main`
(`src/compiler_rust/runtime/src/value/pty.rs`, `interpreter_extern/pty.rs`,
`lib/std/src/sys/pty.spl`). This record exists because the facade limitation is
independent of that decision and will block the next caller who needs a
variadic libc function.
