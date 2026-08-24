# Rust-authority `env -i` drops SystemDrive/SystemRoot — MSVC link fails with a misleading LNK1181

- **Date:** 2026-08-24
- **Status:** FIXED
- **Host:** `MINGW64_NT-10.0-26200`, Git Bash / MSYS, rustc host `x86_64-pc-windows-msvc`
- **Follows:** `bootstrap_unrunnable_on_windows_git_bash_2026-08-24.md` (the lock
  fix; this is the next blocker on the same lane)

## Symptom

With the lock fixed, `--strategy=adhoc --full-bootstrap --stop-after-stage2
--backend=cranelift` reached the Rust seed build and failed:

```
error: linking with `link.exe` failed: exit code: 1181
  = note: LINK : fatal error LNK1181: cannot open input file 'kernel32.lib'
error: could not compile `proc-macro2` / `quote` / `zerocopy` / `getrandom` /
       `serde_core` / `windows_x86_64_gnu` (build script)
error: rust-seed-build failed with exit 101
```

Every failure is a **build script**, which cargo compiles for the HOST
(`x86_64-pc-windows-msvc`) even though the crate targets
`x86_64-pc-windows-gnu`.

The message is a lie in the way that costs the most time: `LIB` was correct and
`kernel32.lib` existed at exactly the path it named
(`.../Windows Kits/10/Lib/10.0.26100.0/um/x64/kernel32.lib`).

## What it was NOT

Ruled out by direct measurement, so the next session does not repeat them:

- **Not `LIB`.** `env -i ... cmd /c echo %LIB%` produced a byte-identical value
  with and without `env -i`.
- **Not link.exe resolution.** Invoking the real linker directly under the same
  `env -i` — `link.exe /LIB /OUT:x.lib kernel32.lib` — succeeded, rc=0.
- **Not `TEMP`.** Already a Windows path; forcing `C:\Windows\Temp` changed
  nothing.
- **Not `SystemRoot` alone.** Supplying it left the failure intact.

## Root cause

Bisected by running the identical `rustc` invocation under `env -i` with the
full 70-variable environment (rc=0) versus the script's forwarded allowlist
(rc=1), then adding back one variable at a time. Exactly two flip it to pass:

```
FIXER: SYSTEMDRIVE = C:
FIXER: ProgramData = C:\ProgramData
```

**`SystemDrive` is required for the MSVC lane.** Without it, drive-rooted `LIB`
entries do not resolve and link.exe reports `LNK1181` on the first library it
tries, regardless of `LIB` being correct.

Compounding it, the capture read only the mixed-case spellings:

```sh
windows_system_root="${SystemRoot:-}"     # EMPTY on MSYS
```

MSYS / Git Bash export the Windows names in **UPPER CASE** (`SYSTEMROOT`,
`SYSTEMDRIVE`, `PROGRAMDATA`); the mixed-case forms a native `cmd` shell carries
do not exist there. So `SystemRoot` was silently empty as well, and the
deliberately hermetic `env -i` handed the toolchain a Windows-less environment.

## Fix

`scripts/bootstrap/bootstrap-from-scratch.sh`:

- capture with upper-case fallbacks —
  `windows_system_root="${SystemRoot:-${SYSTEMROOT:-${WINDIR:-${windir:-}}}}"`;
- add `windows_system_drive` and `windows_program_data` with the same fallback
  shape;
- forward `SystemDrive` and `ProgramData` in **all four** `env -i` cargo
  invocations (llvm on/off × lto on/off), alongside the existing
  `INCLUDE`/`LIB`/`LIBPATH`/`SystemRoot`/`TEMP`.

The hermetic `env -i` is deliberate and is kept; only the allowlist grew.

## Host note — not a repo defect

This machine's `vcvars64.bat` fails with `The system cannot find the path
specified.` even from a clean `cmd`, so a normal VS developer environment cannot
be established here. VC tools (14.44.35207) and the Windows SDK (10.0.26100.0)
are both installed and work when `INCLUDE`/`LIB`/`PATH` are set directly. A
stray `/usr/local/bin/link.exe` (3.2 MB PE) also shadows the real MSVC linker on
`PATH` and must be ordered after it — that shadowing produced the *earlier*
`0xc0000135` (STATUS_DLL_NOT_FOUND) failures, a different error from the
`LNK1181` this record fixes.

## Where the lane stops next — broken host MinGW GCC (NOT a repo defect)

With this fix the seed build gets past every HOST build script and proceeds
through ~130 crates before failing in `ring v0.17.14`, whose build script
compiles C for the `x86_64-pc-windows-gnu` TARGET:

```
warning: ring@0.17.14: Compiler family detection failed due to error:
  ToolExecError: command did not execute successfully (status code exit code: 1):
  "gcc" "-E" ".../detect_compiler_family.c"
error: failed to run custom build command for `ring v0.17.14`
```

The repo is not at fault. This host's MSYS2 MinGW GCC is broken:

| probe | result |
|---|---|
| `gcc --version` | ok, 15.2.0 (Rev8, MSYS2) |
| `gcc -c hello.c -o hello.o` | **rc=1**, zero stdout, zero stderr |
| `gcc -E hello.c` | **rc=1**, zero stdout, zero stderr |
| `cc1.exe --version` (direct) | **rc=127**, zero stderr |

`cc1.exe` exists on disk but cannot load, so the driver fails silently with no
diagnostic at all — which is why `ring` could only report "Compiler family
detection failed". Setting `MSYSTEM=MINGW64` does not change it. Repair the
toolchain on the host (e.g. `pacman -S --needed mingw-w64-x86_64-gcc`) and
re-run the lane; do not work around it in-repo.

**Measure gcc's status without a pipe.** `gcc -c x.c 2>&1 | head -3; echo $?`
reports `head`'s status and reads as a PASS — that misread this exact failure
as success once in this session.

## Also observed on this host (separate, not fixed here)

The deployed `bin/release/x86_64-pc-windows-msvc/simple.exe` (19,455,488 B,
mtime 2026-04-23) **cannot compile or run a program**:

| command | result |
|---|---|
| `--version` | ok, `Simple v0.9.6` |
| `test <dir>` | ok — 13 spec files, 49 passed |
| `run hello.spl` | **exit 127**, zero bytes on stdout and stderr |
| `compile hello.spl` | **exit 139 (SIGSEGV)**, silent |

Reproduced with both MSYS and Windows-form paths, so it is not path
translation. This is the stale-deployed-binary class described in
`.claude/rules/bootstrap.md`; the verdict is a redeploy, which is what the
bootstrap lane above is for. Note `test` passing while `run`/`compile` crash
means **a green `simple test` does not prove the binary can compile anything**.
