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

### Measured 2026-08-24 — a false lead worth recording

`runtime_native.c` was found to fail compilation on Windows with 18 errors
(missing `<direct.h>`, `ATOMIC_VAR_INIT` removed in C23, `timespec_get`
unexposed, POSIX `dlopen` family). That looked like the whole story: the file
defines many `rt_*` symbols and is the FIRST entry in the core-C archive input
list, so "it silently fell out of the archive" was a tidy explanation.

**It was wrong, and the fix did not change the link.** After repairing all 18
errors (landed separately — it is a real bug regardless) and rebuilding the
seed, Stage 2 still reports the identical 68 undefined symbols. Direct
measurement of the linked archive:

```
nm -g --defined-only libsimple_native_all.a | grep -c ' T rt_'   -> 2154
ar t libsimple_native_all.a | grep -c runtime_native             -> 1
nm -g --defined-only ... | grep -c ' T rt_black_box$'            -> 0
```

`runtime_native.o` IS in the archive and 2154 `rt_*` symbols ARE defined. These
68 are simply not among them — some exist only inside POSIX-gated branches, and
at least `rt_black_box` and `rt_host_gpu_active_backend_handle` have no
definition anywhere in `src/runtime/*.c` or `src/compiler_rust/runtime/src`.

### Narrowed further — the core-C archive is never built or linked here

A whole-tree scan settles it. Over every `.a` built in the last 6 hours under
`build/` and `src/compiler_rust/target/`:

```
nm -g --defined-only <each>.a | grep ' T rt_io_udp_recv_from'   -> no hits, anywhere
```

The symbol is in `src/runtime/runtime_native.c` (line ~11363, plus a stub
variant) yet exists in **no built artifact on this machine**. Both archives the
Stage 2 link actually consumes were checked directly:

| archive | `rt_*` defined | has these 68 |
|---|---|---|
| `stage2-runtime-authority/libsimple_native_all.a` | 2154 | no |
| `rust-authority-*/.../libsimple_runtime.a` (newest, post-fix 20:57) | 1944 | no |

The reason is structural, not a coverage gap after all: **`runtime_native.c` is
not in the Rust runtime crate's `build.rs` input list.** It is compiled only by
`build_c_runtime_library` (`native_project/tools.rs`), the `core-c-bootstrap`
bundle path — and that archive is never produced in this lane, so the symbols
never reach the link.

**Next step is therefore a build-pipeline question, not a porting project:** find
why `--runtime-bundle core-c-bootstrap` does not build/link its C archive on
`x86_64-pc-windows-gnu`. Note `setup.shs` warns here that no versioned clang was
found and the C runtime falls back to a bare host `clang/cc`, which is a
plausible thread to pull first.

Three readings of this were tried in one session — coverage gap, compile
failure, coverage gap again — before the whole-tree `nm` scan settled it. Run
that scan FIRST next time; it is one command and it is decisive.

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

### FINAL diagnosis — the symbols are undefined on EVERY platform; only Windows enforces it

The core-C archive is a red herring too. For a `bootstrap_main` entry — which is
exactly what Stage 2 builds — `native_project/config.rs` takes this branch:

```rust
if is_bootstrap_main_entry(&self.entry_file) {
    if let Some(native_all) = bootstrap_hosted_native_all_runtime(...) {
        return Ok(Some((native_all, true)));   // libsimple_native_all.a
    }
}
```

so `build_core_c_runtime_library` is never reached and `libsimple_native_all.a`
is the runtime. The 68 symbols are therefore expected to come from the Rust
runtime crate — and they are not there either:

```
grep -rn 'rt_io_udp_recv_from\|rt_black_box' src/compiler_rust/runtime/src --include=*.rs
  -> no matches
```

**These 68 names are defined in no C archive, no Rust source, and no built
artifact — on any platform.** Linux does not fail on them because, as
`.claude/rules/vcs.md` already records for `check-no-unresolved-runtime-symbols.shs`,
"the native link tolerated the undefined symbol ... and the NULL GOT slot became
a SIGSEGV". ELF lazy binding defers the error to runtime. Windows PE has no
equivalent tolerance: every symbol must resolve at link time, so the same defect
is a hard error here.

**This is not a Windows porting gap. Windows is CATCHING a latent repo-wide
defect that Linux links past and pays for later as a runtime SIGSEGV** — the
identical failure mode that bug already describes for `rt_unwrap_or_trap`.

Consequences for whoever picks this up:
- the fix is to implement or explicitly trap all 68 names, which benefits every
  platform, not just Windows;
- `check-no-unresolved-runtime-symbols.shs` should be promoted from ADVISORY
  once a Windows link exists, because the Windows link is a far stronger oracle
  for this class than `nm` on a tolerant ELF binary;
- do NOT "fix" it with `-Wl,--unresolved-symbols=ignore-all` or an equivalent;
  that reproduces the Linux behaviour and converts a caught link error back into
  a latent runtime SIGSEGV.
