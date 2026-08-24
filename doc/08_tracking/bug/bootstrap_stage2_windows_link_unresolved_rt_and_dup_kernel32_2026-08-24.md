# Stage 2 on Windows reaches the LINK and fails there: 68 unresolved `rt_*` + 22 duplicate kernel32 symbols

- **Date:** 2026-08-24
- **Status:** OPEN — this is where the Windows bootstrap lane now stops
- **Host:** `MINGW64_NT-10.0-26200`, Git Bash / MSYS, `x86_64-pc-windows-gnu`, cranelift
- **Lane:** `bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 --backend=cranelift`
- **Follows:** `bootstrap_unrunnable_on_windows_git_bash_2026-08-24.md`,
  `bootstrap_env_i_drops_systemdrive_msvc_link_2026-08-24.md`

## What now works (was previously unreachable)

The lane used to die before starting. It now:

1. acquires its output lock (`/proc` fallback for MSYS `ps`);
2. builds the **entire Rust seed** — all four cargo passes, 0 errors
   (`Finished bootstrap profile [optimized] in ~5m`);
3. publishes the seed and preserves a phase-1 snapshot;
4. runs Stage 2, which **compiles every module** and reaches the final link.

That last point is the new frontier: Stage 2 no longer fails at compile, it
fails at link.

## Blocker A — 68 unresolved `rt_*` symbols

```
ld.exe: libspl_objects.a(mod_702.o):simple_module:(.rdata$.refptr+0x0):
  undefined reference to `rt_io_udp_recv_from'
```

68 distinct names (`sort -u`), including `rt_black_box`,
`rt_event_ports_{create,close,poll,register,deregister}`,
`rt_io_udp_{send_to,recv_from}`, `rt_io_tcp_write_bytes`,
`rt_host_gpu_active_backend_handle`.

**This is not the stale "83 undefined codegen names" note.** That figure was
already corrected: `check-no-unresolved-runtime-symbols.shs` re-measured GREEN
on 2026-08-23 (`PASS — 196 symbol(s) checked across 0 binary(ies) + archive, 0
unresolved`). The archive is complete **on Linux**. These 68 are a genuine
**Windows runtime-coverage gap** — codegen emits calls the C/Rust runtime only
implements for POSIX. Reproducing it needs a Windows link, which is exactly what
no lane could reach until now, which is why it has never been seen.

Fixing it means implementing or explicitly trapping ~68 runtime entry points for
Windows. That is a porting project, not a patch.

## Blocker B — 22 `multiple definition` errors from the kernel32 import stubs

```
ld.exe: libsimple_native_all.a(kernel32.dlls00001.o):(.text+0x0):
  multiple definition of `GetLastError';
  libsimple_native_all.a(kernel32.dlls00260.o):(.text+0x0): first defined here
```

The Rust staticlib embeds kernel32 import stubs more than once and MinGW `ld`
rejects the collision. 22 occurrences. Plausible remedies —
`-Wl,--allow-multiple-definition`, deduplicating the import members, or linking
the import library separately — are a **linker-contract decision** for whoever
owns the native link, not something to pick unilaterally: `--allow-multiple-definition`
silences a real ODR violation and could mask a genuine duplicate later.

## Do not misread the progress

`simple test` passing proves nothing about this. On the deployed Windows binary
`test` runs 49 tests green while `run` exits 127 and `compile` SIGSEGVs. Stage 2
compiling every module likewise does not mean the lane is close to done — the
link is a distinct wall with two independent causes above.

## Reproduce

```sh
# host env (this machine): real MSVC linker ahead of the stray /usr/local/bin/link.exe,
# and the MSYS2 mingw64 tree ahead of Git Bash's own /mingw64/bin
export PATH="/c/dev/tool/msys2/mingw64/bin:$PATH"
sh scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap \
  --stop-after-stage2 --backend=cranelift --output=build/bootstrap
# then read, WITHOUT a pipe (a pipe launders the status):
#   build/bootstrap/logs/x86_64-pc-windows-gnu/stage2-native-build.log
```

## Adjacent finding, not fixed here

`check-bootstrap-portability.shs` fails `MinGW runtime DLL is not staged`, and
this is a **regression, not a stale guard**: `origin/ci/adhoc-bootstrap-st4` (0
commits ahead of main, i.e. fully contained in it) still carries the
`simple_runtime.dll` staging loop, and `9a0cfd1e5d` ("harden staged native
compilation", 2026-08-10) deleted it as collateral in a session-guard rewrite.
The DLL **is** produced by the build. Restoring it is not a plain `cp` revert:
main replaced that loop with `bootstrap_stage3_prepare_seed_generation`, a
hash-recorded immutable artifact set, so the DLL has to join that published
list. Deserves its own reviewed change.
