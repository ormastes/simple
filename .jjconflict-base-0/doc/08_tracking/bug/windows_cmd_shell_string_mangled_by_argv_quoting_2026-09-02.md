# Windows: any `process_run("cmd", ["/C", s])` with a quote in `s` is mangled

- **Filed:** 2026-09-02
- **Status:** OPEN (one instance FIXED at the call site; the general hazard remains)
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

## Still open

1. **The runtime has no shell-string spawn.** Every caller that wants a cmd.exe
   command line has to route it through an argv quoter that will corrupt it.
   Either add a raw-command-line spawn entry point, or special-case cmd.exe in
   `win_cmd_build_line`.
2. **`backend_shell_tuple` in `src/compiler/70.backend/backend/runtime_compiler.spl`
   is a live instance.** The runtime-object cache hit and publish paths build
   `cp -f '<path>' '<path>'` and `mv -f ... ...` strings. Those use single
   quotes, which cmd.exe does not treat as quoting at all, and `cp`/`mv` are not
   cmd builtins — so on Windows the object cache silently never hits and never
   publishes. Latent (correctness is unaffected, only speed), not measured in
   isolation yet.

## Cross-platform

`msvc.spl` is reached only on the Windows/MSVC link path. `win_cmd_build_line`
is inside `#ifdef _WIN32` platform code. Nothing here affects Linux, macOS,
FreeBSD or the mingw lane.
