# Windows: any `process_run("cmd", ["/C", s])` with a quote in `s` is mangled

- **Filed:** 2026-09-02
- **Status:** FIXED for the native C runtime 2026-09-06 (general boundary fix,
  measured — see "Fix (2026-09-06)"). Two residuals remain, both filed below:
  the Rust bootstrap seed's own spawn path, and the `cp`/`mv` shell strings in
  `backend_shell_tuple` (a *different* defect: those commands are not cmd
  builtins at all).
- **Lane:** Windows MSVC bootstrap, Stage 2 receiver probe

## Defect

`src/runtime/platform/windows_command_line_private.h` `win_cmd_build_line()`
builds the child command line using **CommandLineToArgvW / MSVCRT** quoting: an
argument containing a space or a quote is wrapped in `"` and every embedded `"`
is escaped as `\"`.

That is correct for ordinary CRT programs. **cmd.exe is not one.** It parses its
own command line and does **not** honour `\"`. So a shell string that contains a
quote — the normal case whenever a path has a space — arrives mangled.

## Measurement (2026-09-02)

Standalone `CreateProcessA` harness calling the real `win_cmd_build_line`
(`/d/simple_build/cmdtest/t.c`), argument `/C` plus the exact string
`src/compiler/70.backend/linker/msvc.spl` was producing:

```
CMDLINE=[cmd /C "\"C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.44.35207\bin\Hostx64\x64\link.exe\" /NOLOGO > \"D:\simple_build\cmdtest\out.log\" 2>&1"]
The filename, directory name, or volume label syntax is incorrect.
rc=1
```

The linker never ran and the redirect target was never created. On the lane this
surfaced as `[msvc-link] FAILED exit=1` followed by
`<link log unreadable: ...guard.link.log>` — a failure with no diagnosis, which
was twice misread as a linker error and once as corrupted process capture.

## Fixed instance

`src/compiler/70.backend/linker/msvc.spl` — both `MsvcLinker.link` and the
lld-link path now invoke the linker **directly by argv** (`msvc_run_argv`), which
is the quoter's intended consumer. `msvc_shell` is retained only for the
quote-free `where <tool> 2>nul` probes and carries a warning comment.

## Fix (2026-09-06)

Taken at the single boundary every Windows spawn already funnels through —
`win_cmd_build_line` in `src/runtime/platform/windows_command_line_private.h`,
reached from `runtime_process.c:343` (bounded `process_run`), `:632` (piped
spawn) and `platform_win.h:720` (`rt_windows_build_command_line`). One helper,
so the ~15 `process_run("cmd", ["/C", …])` call sites across `src/app/**`,
`src/lib/**` and `src/compiler/**` are all covered without touching any of them.

Mechanism: the documented cmd.exe contract for a verbatim shell string is `/S`
— with `/S`, cmd strips exactly the first and last quote after `/C` (or `/K`)
and preserves everything between them byte-for-byte. So `cmd /S /C "<payload>"`.

Deliberately narrow. It fires only when **all** of: the executable's basename is
`cmd`/`cmd.exe` (case-insensitive), `arg_count == 2`, `args[0]` is `/c /C /k /K`
(or the `-` form), **and the payload actually contains a `"`** — i.e. exactly the
set of strings that are mangled today, and nothing else. The quote requirement
is load-bearing, not cosmetic: `cmd /c "C:\p ath\run.bat"` (spaces, no quotes)
works today via cmd's two-quote heuristic, and `/S` *disables* that heuristic,
so an unconditional `/S` would have regressed it. Everything else keeps the
legacy CommandLineToArgvW path unchanged.

Fail-closed, not convenient: a matching payload containing CR or LF cannot be
represented on a Windows command line, so `win_cmd_build_line` returns NULL
(the caller surfaces it as a spawn failure) rather than letting the child run a
silently truncated *prefix* of what was asked for. At a shell boundary the
truncated-prefix outcome is the dangerous one.

### Measured, Windows 11, 2026-09-06

Standalone `CreateProcessA` harness over the **real** `win_cmd_build_line`
(same method as the 2026-09-02 measurement), payload
`echo hello "a b c" ^^ and & echo second`:

```
BEFORE
CMDLINE=[cmd /C "echo hello \"a b c\" ^^ and & echo second"]
hello \"a b c\" ^ and            <- quotes corrupted, `\` leaked into output
second
rc=0

AFTER
CMDLINE=[cmd /S /C "echo hello "a b c" ^^ and & echo second"]
hello "a b c" ^ and              <- verbatim
second
rc=0
```

Three more cases on the fixed builder:

| case | payload | result |
|---|---|---|
| quoted exe path w/ spaces | `echo "C:\Program Files\x\link.exe" /NOLOGO` | `"C:\Program Files\x\link.exe" /NOLOGO`, rc=0 (was `\"C:\Program Files…\"`) |
| **regression guard** | `C:\Windows\Temp\sp test\run.bat` (spaces, no quote) | legacy path kept, `BAT-RAN`, rc=0 |
| CR/LF payload | `echo "a"<LF>echo INJECTED` | builder returns NULL — spawn refused, `INJECTED` never runs |

Pinned by `test/01_unit/runtime/process_run_timeout_provider_source_spec.spl`
(`it "hands cmd.exe a quoted shell string verbatim via /S"`). The pin is a
source contract, not a live round trip, because the deployed `bin/simple` on the
Windows box is the Rust seed — see residual 1.

`src/compiler/70.backend/linker/msvc.spl`'s "MUST NOT CONTAIN A DOUBLE QUOTE"
warning is now stale and was updated; its `msvc_shell("dir /b \"{path}\" 2>nul")`
probes at :265/:310/:325 had already been violating it and are correct on the
native runtime as of this fix.

## Still open

1. **The Rust bootstrap seed has the same bug on its own spawn path.** The fix
   above is in the C runtime; the seed spawns through `std::process::Command`,
   whose Windows implementation applies the same CommandLineToArgvW quoting and
   has no cmd.exe special case. Measured 2026-09-06 with the deployed
   `bin/simple` (a seed): `process_run("cmd", ["/C", "echo hello \"a b c\" and"])`
   printed `hello \"a b c\" and`. Per repo policy the seed is bootstrap-only, so
   this is recorded rather than patched here; it does mean any lane still driven
   by the seed keeps the old behaviour until a self-hosted binary is deployed.
2. **`backend_shell_tuple` in `src/compiler/70.backend/backend/runtime_compiler.spl`
   is a live instance.** The runtime-object cache hit and publish paths build
   `cp -f '<path>' '<path>'` and `mv -f ... ...` strings. Those use single
   quotes, which cmd.exe does not treat as quoting at all, and `cp`/`mv` are not
   cmd builtins — so on Windows the object cache silently never hits and never
   publishes. Latent (correctness is unaffected, only speed), not measured in
   isolation yet. **Not addressed by the 2026-09-06 fix and not addressable by
   it:** that fix makes cmd.exe receive the string verbatim, which is exactly
   what those call sites already needed least — the string is still `cp`/`mv`,
   which cmd.exe does not have. This needs a `copy`/`move` (or argv) branch.

## Cross-platform

`msvc.spl` is reached only on the Windows/MSVC link path. `win_cmd_build_line`
is inside `#ifdef _WIN32` platform code. Nothing here affects Linux, macOS,
FreeBSD or the mingw lane.
