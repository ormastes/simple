# Stage 2 on Windows reaches the LINK and fails there: 68 unresolved `rt_*` + 22 duplicate kernel32 symbols

- **Date:** 2026-08-24
- **Status:** Blocker A (68 unresolved `rt_*`) — MEASURED RESOLVED on the GNU
  lane 2026-09-01 by the same fix that closed the MSVC lane's 98. Blocker B
  (duplicate kernel32) — mitigated by inspection, not yet link-verified on
  GNU. See "2026-09-01 — Blocker A confirmed resolved on the GNU lane" below.
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

### Where the 68 signatures live (for whoever implements them)

They are NOT in `src/compiler_rust/common/src/runtime_symbols.rs` (checked: 0
hits for all four probes). The authoritative source is the Simple `extern`
declarations that generate the calls:

```
src/lib/common/crypto/constant_time.spl:7      extern fn rt_black_box(value: i64) -> i64?
src/lib/nogc_async_mut/io/platform_event.spl:147  extern fn rt_event_ports_create() -> i64
src/lib/nogc_sync_mut/io/udp.spl:223           extern fn rt_io_udp_recv_from(fd: i64, size: i64) -> ([u8], text)?
```

Enumerate the full set with:

```sh
grep -rn "extern fn rt_" src/lib src/compiler src/app --include=*.spl
```

**Why this was NOT mass-generated into trap stubs in one pass.** The shapes are
not uniform. `rt_event_ports_create() -> i64` is trivial, but
`rt_io_udp_recv_from(...) -> ([u8], text)?` returns an OPTIONAL OF A TUPLE, and
guessing how that lowers to the C ABI (sret pointer? packed struct? discriminant
placement?) risks silent memory corruption at every call site — strictly worse
than the link error it would replace, and it would pass the link while
misbehaving at runtime. Derive each return shape from the actual lowering, not
by inspection, and add them in batches with a link check per batch.

### The 68 split into TWO different problems (measured)

Classified against the linked archive and the C sources:

| group | count | what it needs |
|---|---|---|
| defined in C, but the defining file is not compiled into the linked archive | **31** | a BUILD-CONFIG fix |
| no definition in any C source at all | **37** | real IMPLEMENTATION |
| present in `libsimple_native_all.a` already | **0** | — |

The 31 live in `runtime_native.c` (25) and `runtime.c` (5). Neither is in the
Rust runtime crate's `build.rs` list, and the `core-c-bootstrap` archive path is
never reached for a `bootstrap_main` entry (see above), so neither file reaches
the link. Note `runtime.c` also still fails to compile here under gcc, so it
needs both a compile fix and the build-config fix.

The 37 have no definition anywhere and must be written. Their return shapes are
NOT uniform — measured across the 68: 13 `bool`, 11 `i64`, 3 `f32`, 3 `text`,
3 `[u8]`, 3 `[i64]`, and **26 SIMD vector returns** (`Vec8f`, `Vec4u64`,
`Vec4u32`, `Vec4d`, `Vec4f`, `Vec4i64`), plus optional-of-tuple shapes like
`([u8], text)?`.

The SIMD returns are the reason this must not be batch-guessed: vector return
ABI (register class, alignment, whether it is returned in XMM/YMM or via sret)
is exactly where a plausible-looking stub links cleanly and then corrupts state
at every call site.

**Suggested order for whoever takes this:** fix the 31 first — it is a
build-config change with an immediate, checkable signal (the undefined count
should drop 68 -> 37) — then implement the 37 in shape-groups, scalars first,
SIMD last, re-linking after each group.

### The "just add runtime_native.c to the archive" fix is DISPROVEN (measured)

Two corrections to the analysis above, both from direct measurement.

**1. `runtime_native.o` is not in the archive at all.** An earlier
`ar t libsimple_native_all.a | grep -c runtime_native` returned 1 and was read as
"the object is present". It is not — the member that matched is
`37be46648adf0aaa-runtime_native_gpu_stub.o`, a different file. `runtime_native.c`
is absent entirely. Match on the exact member name, not a substring.

**2. Adding it would collide 475 ways.** Compiled standalone and compared
against the archive's existing definitions:

```
gcc -c -O1 -I src/runtime src/runtime/runtime_native.c -o rn.o     # rc=0
nm -g --defined-only rn.o        | awk '$2=="T"{print $3}' | sort -u   -> 681
nm -g --defined-only <archive>   | awk '$2=="T"{print $3}' | sort -u   -> 38203
comm -12 <those two>                                                   -> 475
```

475 of the 681 symbols `runtime_native.c` defines are ALREADY defined in
`libsimple_native_all.a` (`copy_mem`, `panic`, `print_raw`, `rt_actor_join`,
`rt_actor_recv`, ...). Adding the file to the link or to a build list therefore
trades 31 undefined symbols for 475 duplicate-definition errors — the same class
as Blocker B, at 20x the size.

**So the 31/37 split above, while numerically correct, does NOT imply the 31 are
the easy half.** Both halves are architectural:

- the archive's existing definitions come from the Rust runtime crate, and
  `runtime_native.c` is a parallel C implementation of largely the same surface
  (this is the documented "two families / first-definition-wins" arrangement
  referenced in `runtime_memory_guard.h`'s header);
- resolving the 31 means deciding WHICH implementation owns those names on
  Windows, not merely compiling one more file.

Do not attempt the build-config route as a quick win. Measure the overlap first
with the three commands above; it takes under a minute and it is decisive.


## 2026-08-30 — Blocker A root-caused and fixed on the MSVC lane

The 2026-08-24 conclusion ("a build-pipeline question: find why
`--runtime-bundle core-c-bootstrap` does not build/link its C archive") was the
right thread. Pulled on the **MSVC** lane it ends in a compile failure, not a
pipeline gap: `runtime_native.c` **does not compile under clang-cl**, so the
core-C archive can never be produced and every symbol the file defines is
absent from the link.

Measured, `clang-cl 18.1.8`, reading the compiler's status directly (not
through a pipe — a piped `rc` reports `head`'s status and reads as success):

| stage | errors | cause |
|---|---|---|
| initial | 1 fatal | `runtime_native.c:32` `#include <unistd.h>` — MSVC has none |
| after guarding it | 21 | `ssize_t` (supplied by `unistd.h`) |
| after `SSIZE_T` typedef | 11 | `popen`/`pclose`/`ftruncate`/`clock_gettime`; `__cpuid` macro-vs-function |
| after shims | 5 | `__get_cpuid` / `__get_cpuid_count` unavailable under clang-cl |
| after cpuid gating | **0** | compiles clean |

The cpuid failures were an ordering bug worth naming: `runtime_simd_dispatch.h`
tested `defined(__GNUC__) || defined(__clang__)` **before** `defined(_MSC_VER)`,
and **clang-cl defines both**. So it took the GNU branch, pulled GCC's
`<cpuid.h>` (whose `__cpuid` is a 5-argument macro), and that collided with the
2-argument `__cpuid` function in MSVC's `<intrin.h>`. Correct MSVC branches
already existed at all five call sites — they were simply unreachable.
`runtime_native.c`'s own cpuid guard had the order right, which is why only the
header was wrong.

Result: the object now defines **929** `rt_*` symbols, including
`rt_io_udp_bind`, `rt_iocp_create` and `rt_io_tcp_write_bytes` — three of the
names this record lists as undefined.

**`rt_black_box` is NOT fixed** and is not fixable this way: as this record
already established, it has no definition anywhere in `src/runtime/*.c` or
`src/compiler_rust/runtime/src`. Same for `rt_host_gpu_active_backend_handle`.
Those remain genuinely missing implementations.

Every change is gated on `_MSC_VER`, never `_WIN32`: MinGW supplies `unistd.h`,
`popen`, `ftruncate` and `clock_gettime` itself, and widening the guard would
shadow them. Verified both ways — clang-cl 0 errors, MinGW `gcc` still compiles
the file and emits an object.

**Blocker B (duplicate kernel32 import descriptors) is untouched** and now
appears on MSVC too, as `LNK2005 __IMPORT_DESCRIPTOR_kernel32`. This record's
judgement stands: it is a linker-contract decision, not a unilateral one.

## 2026-09-01 — Blocker A confirmed resolved on the GNU lane (measured, no full bootstrap needed)

A full `--strategy=adhoc --full-bootstrap --stop-after-stage2` GNU-lane run was
started (`build/bootstrap-gnu`, PID tree rooted at cargo.exe 2812) and then
deliberately killed partway through the Rust seed build: it is a ~15+ minute
run and mostly rebuilds things irrelevant to this question. A cheaper static
method answers the same question directly, without a link:

1. Take the **cross-object undefined symbol set** out of the newest already-built
   `libspl_objects.a` from the MSVC lane
   (`build/w/stage3/x86_64-pc-windows-msvc/native-objects-EYz9n4/libspl_objects.a`,
   the object archive Stage 2 actually links). This archive is produced by the
   Rust seed compiling ordinary Simple source — the undefined symbol NAMES it
   references are target-ABI-independent (x86_64 Windows uses the same
   unmangled `extern "C"` names on both the `-msvc` and `-gnu` triples, no
   leading-underscore quirk), so it is a valid proxy for what the GNU lane's own
   `libspl_objects.a` would reference, without having to build one:
   ```
   llvm-nm --undefined-only libspl_objects.a | ... -> u.sym   (6,271)
   llvm-nm --defined-only   libspl_objects.a | ... -> d.sym   (23,921)
   comm -23 u.sym d.sym -> need.sym                            (522, of which 508 rt_*)
   ```
2. Subtract what the Rust-hosted runtime (`simple_native_all.lib`, 343,746
   defined symbols, same source-name argument as above) already supplies:
   `comm -23 need_rt.sym rt_native_all.sym` -> **71 names** still needing the
   core-C supplement. This 71 is a superset of the original 68 (68 was counted
   2026-08-24 before several of these names existed as codegen call sites; the
   task's 5-name sample — `rt_io_udp_recv_from`, `rt_black_box`,
   `rt_event_ports_deregister`, `rt_io_tcp_write_bytes`,
   `rt_host_gpu_active_backend_handle` — cross-checked individually: the first
   two and the last are satisfied straight from `simple_native_all.lib` and
   never reach the supplement at all; the middle two are in the 71).
3. Compile the exact 17-file core-C supplement TU list from
   `native_project/tools.rs:341-413` (`build_core_c_runtime_library`) with the
   real MinGW toolchain on this box (`PATH=/c/dev/tool/msys2/mingw64/bin`,
   `gcc.exe (Rev8) 15.2.0`):
   ```
   for f in runtime_native.c runtime_framebuffer.c runtime_directx_core.c \
     runtime_legacy_core.c runtime_core_io_exports.c runtime_core_host_services.c \
     runtime_fork.c runtime_memtrack.c runtime_process.c runtime_contracts.c \
     runtime_font.c runtime_thread.c runtime_simd_utf8.c runtime_simd_case.c \
     runtime_simd_dispatch.c runtime_packed_span.c runtime_core_exports.c; do
     gcc -c -O1 -I . -o "$out/${f%.c}.o" "$f"
   done
   ```
   **Result: 0 compile errors across all 17 files.** (`runtime_terminal.c` was
   also in the list but compiled along with the rest — same result.)
4. Compare the 71 against what those 17 objects define:
   ```
   nm *.o | awk '$2=="T"||$2=="t"{print $3}' | sort -u -> gnu_defined_strong.sym  (1,303)
   nm *.o | awk '$2=="W"||$2=="w"{print $3}' | sort -u -> gnu_defined_weak.sym    (0)
   comm -23 unres1.sym gnu_defined_strong.sym -> still_missing.sym               (0)
   ```

### Classification of the 71 (superset of the 68)

| class | n | evidence |
|---|---|---|
| (a) defined nowhere | **0** | all 71 appear as strong `T`/`t` symbols in the compiled `.o` set |
| (b) defined but TU not in the GNU lane's source list | **0** | the registration in `tools.rs` is `cfg!(target_os = "windows")`-gated, not linker-flavor-gated — the same 17-file list is used for `-msvc` and `-gnu` alike; verified by reading `linker.rs:1588-1665`, whose branch condition is `cfg!(target_os = "windows") && runtime_bundle_requests_core_c_bootstrap(...)` with no MSVC-only qualifier |
| (c) defined but weak (never resolves cross-TU, the `rt_set_args` class) | **0** | `nm` symbol-type scan of all 17 compiled objects found zero `W`/`w` symbols of any kind, `rt_*` or otherwise |
| (d) POSIX-gated out on Windows | **0** | empirical, not inferential: these are the actual objects gcc produced when compiling the real sources with the real mingw64 toolchain on this Windows box — a POSIX-gated definition could not have appeared as a strong symbol in that output |

**Blocker A is therefore already resolved on the GNU lane**, by the identical
mechanism that resolved the MSVC lane's 98 (commits `a3aac936699`,
`bb397d8d147`, `2574f1fe161`, `68dce16e354`, `8df1989a431` — none of them
`#ifdef`/`cfg`-restricted to MSVC). The MSVC-lane session record's own
diagnosis under "Blocker A root-caused and fixed on the MSVC lane" already
predicted this for the *compile* half ("Verified both ways — clang-cl 0
errors, MinGW `gcc` still compiles the file and emits an object"); this entry
extends that to the *full 71-symbol coverage* question, not just
`runtime_native.c` alone.

**What this does NOT verify:** an actual GNU-lane link. `libspl_objects.a` was
reused from the MSVC lane rather than rebuilt for `-gnu` (avoiding the ~15 min
rebuild), so this is a strong static proof, not a link transcript. Given
`Array.data_ptr`/`OutlineModule.*_push`/`str.*`/`LazyInstantiator.*` (groups
A/B/H of `stage2_windows_unresolved_inventory_2026-08-31.md`) no longer appear
in `need.sym` at all, those codegen-side fixes are confirmed landed too.

### Blocker B (duplicate kernel32 import stubs) — mitigated by inspection, not link-verified

`linker.rs:1588-1665` picks the duplicate-definition escape by `is_msvc`
(`uses_msvc_flags(target.linker_flavor())`): `/FORCE:MULTIPLE` for MSVC/
clang-cl, **`-Wl,--allow-multiple-definition` for everything else** — which is
a real, valid `ld.bfd`/`ld.gold`/mingw-`ld` flag and covers the GNU lane. This
flag is applied to the whole link, so it should suppress the 22 duplicate
`kernel32` stub definitions the same way it suppresses the `rt_*` overlap
between `simple_native_all.lib` and the core-C supplement. This was **not**
empirically verified — doing so needs an actual duplicate-symbol GNU link,
which needs the full `simple_native_all` archive built for `-gnu` (the
expensive path this entry avoided for Blocker A). Left open for whoever runs
the next real GNU-lane bootstrap to confirm from the link log.

### Unix impact

None. Every file involved (`native_project/tools.rs`'s TU list,
`runtime_core_exports.c`, `runtime_core_io_exports.c`,
`runtime_core_host_services.c`, and friends) already compiles on Linux/macOS
today as part of the same unconditional list, and no code changed in this
session — this entry is a measurement, not a patch. No new TU was added, no
existing TU was modified.
