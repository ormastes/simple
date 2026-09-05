# Windows seed fingerprint fails mute on `llvm-config --libfiles`; and fingerprints a different LLVM than the build links

**Date:** 2026-08-30
**Status:** Defect 1 FIXED in this change; Defect 2 OPEN
**Host:** Windows 11, MSYS2, `x86_64-pc-windows-gnu` lane

## Defect 1 (fixed) — silent `return 1`, no offending path anywhere

`sh scripts/bootstrap/bootstrap-from-scratch.sh windows-entry --mingw
--full-bootstrap --stop-after-stage2` died after ~10 minutes with exactly one
line of explanation:

```
error: failed to fingerprint Rust seed inputs
```

The error manifest it wrote carried no cause either — the captured stderr file
was **0 bytes**:

```
schema=simple-bootstrap-fingerprint-error-v1
phase=pre
status=1
```

Root cause, found only by re-running the function under `sh -x`:
`bootstrap_stage3_resolve_llvm_build_authority`
(`scripts/check/lib/bootstrap-stage3/authority.shs`) captures
`llvm-config --link-static --libfiles` and then requires every entry to be
POSIX-absolute:

```sh
case "$bootstrap_stage3_llvm_lib" in
    /*) ;;
    *) return 1 ;;   # <- no message, ever
esac
```

On MSYS2, `llvm-config` is a **native Windows** program and reports native
drive-letter paths:

```
C:/dev/tool/msys2/mingw64/lib/libLLVMWindowsManifest.a ... (194 libraries)
```

so the guard rejected the **first** library and returned 1. Sibling values
escaped the same fate only by accident: `--prefix` and `--libdir` are laundered
through `cd -- ... && pwd -P`, which accepts a drive path and emits a POSIX one.
`--libfiles` is consumed literally.

This is the fail-mute class the repo's guard-verdict conventions exist to kill:
a bootstrap authority returning a bare 1 with the deciding value in no log, no
manifest, and no stderr. Ten minutes of hashing were spent before the failure,
and the diagnosis required tracing the function by hand.

**Fix (this change):** normalize `--libfiles` through `cygpath -u` under the
`MSYS*|MINGW*|CYGWIN*` uname case (the precedent `command-snapshot.shs` already
uses), once at the capture point, so no downstream consumer changes; and make
the absolute-path guard print the offending path to stderr before returning.
Verified: the fingerprint returns **RC=0** on this host after the change.

## Defect 2 (OPEN) — the fingerprint tracks a different LLVM than the build

`bootstrap_stage3_resolve_llvm_build_authority` selects its LLVM with a plain
`command -v llvm-config` against the passed PATH. There is no ABI or version
preference in that resolution. Meanwhile the bootstrap itself resolves LLVM via
`scripts/setup/platform-detect.shs`, which honours `LLVM_SYS_<major>0_PREFIX`.

On this host the two disagree, and the disagreement is decided purely by PATH
ordering:

| consumer | LLVM chosen | why |
|---|---|---|
| build (`platform-detect.shs`) | **18.1.8**, `/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc` | `LLVM_SYS_180_PREFIX` |
| seed fingerprint (`authority.shs`) | **21**, `/c/dev/tool/msys2/mingw64` | `command -v`; msys2 is PATH position 2, the LLVM 18 dir is position 39 |

The fingerprint exists to decide whether the Rust seed is stale by CONTENT. It
therefore hashes `llvm-config`, its 194 static libraries, and the LLVM version —
**of an LLVM the build never links**. Consequences:

- a change to the LLVM the build actually uses does not perturb the fingerprint,
  so a genuinely stale seed can be judged fresh — the exact failure the
  content-hash gate replaced mtime checks to prevent;
- the recorded provenance names the wrong toolchain, which the Windows plan's
  §4 "immutable inputs" gate depends on being exact;
- reordering PATH silently changes the fingerprint with no source change.

Not fixed here because the correct resolution is a policy question owned by the
bootstrap authority: either the fingerprint honours `LLVM_SYS_*_PREFIX` (matching
the build), or the build and fingerprint share one resolver. Workaround in the
meantime is to put the intended LLVM's `bin` first on PATH — fragile and
undocumented, which is why this is filed rather than left as tribal knowledge.

## Defect 3 (OPEN) — MSVC-style `--system-libs` tokens are unresolvable, and were also silent

With the libfiles guard fixed, putting the **MSVC-built LLVM 18** first on PATH
advances past all 183 libraries and then fails in the system-libs loop. The two
`llvm-config` builds on this host disagree in FORM, not just version:

```
MSVC LLVM 18 : psapi.lib shell32.lib ole32.lib uuid.lib advapi32.lib ws2_32.lib libxml2s.lib
msys2 LLVM 21: -lpsapi -lshell32 -lole32 -luuid -ladvapi32 -lws2_32 -lntdll -lpthread -lz -lzstd.dll -lxml2
```

The token loop handles `-lfoo`, an absolute path, and `-framework`; everything
else fell through to `-*) return 1 ;;` / `*) return 1 ;;` — silent again. Bare
`<name>.lib` tokens resolve against the Windows SDK library path, which this
authority never captures (only macOS SDK identity is recorded, via `xcrun`), so
binding them is not possible today without deciding how SDK identity enters the
receipt.

**Now IMPLEMENTED** (it became blocking once the lane moved to MSVC: pointing
`llvm-sys v180.0.0` at msys2's LLVM 21 headers fails, so the MSVC lane must use
the MSVC `llvm-config`, whose tokens this branch had to accept). `<name>.lib`
tokens are resolved the way the linker resolves them — LLVM's own libdir first,
then each entry of the MSVC `LIB` search path — and the resolved file is hashed
into the receipt. That makes the MSVC record STRONGER than the GNU one: it names
the exact Windows SDK import libraries linked, which §4 of the plan wants and
which nothing previously captured.

Three sh portability traps were hit writing it, each silent:

- iterating the directory list with an unquoted `for` word-split every path
  containing a space — i.e. all of them (`Program Files`);
- `printf '%s' "$LIB"` leaves the last entry unterminated and `while read`
  discards it, which dropped the SDK `um/x64` directory — the one holding
  `psapi.lib`;
- `printf` with a literal Windows path eats `2` as an octal escape and
  `` as a vertical tab (this bit the vcvars capture, not the guard).

## Defect 4 (BLOCKED) — the gnu lane cannot build the Rust seed on this host

Not a code defect; a host capability gap, recorded because the Windows plan
requires a blocked lane to be stated rather than quietly abandoned.

With the fingerprint fixed and gcc repaired (see the host note below), the seed
build reached the **link** step and failed there for two INDEPENDENT reasons:

1. **No gnu-ABI LLVM 18.** `src/compiler_rust/compiler/Cargo.toml:123` pins
   `inkwell = { version = "0.5", features = ["llvm18-0"] }`. This host has
   msys2 LLVM **21** (gnu) and LLVM **18** (MSVC-built) — no gnu 18. `llvm-sys`
   therefore linked against 21 and inkwell's 18-era entry points are gone:

   ```
   undefined reference to `LLVMDIBuilderInsertDeclareAtEnd'
   undefined reference to `LLVMConstFCmp' / `LLVMConstNSWMul' / `LLVMConstICmp'
   ```

   plus `ffi_*` (no libffi) and `__imp_isblank`.

2. **Mixed mingw C runtimes.** Independent of LLVM, and it would survive a
   backend change:

   ```
   multiple definition of `pthread_self';
     msys2 libpthread.a(libwinpthread_la-thread.o)
     vs libpthread.dll.a(libwinpthread_1_dll_d000123.o) first defined here
   ```

   Rust's bundled mingw runtime and msys2's system gcc runtime both supply it.

Note the ring build log records `HOST=x86_64-pc-windows-msvc` /
`TARGET=x86_64-pc-windows-gnu` — the gnu lane is a CROSS build on this host.

**Resolution: the gnu lane is blocked here and the MSVC lane is used instead.**
The MSVC lane is internally consistent on this machine: rustc host is
`x86_64-pc-windows-msvc`, the available LLVM 18 is MSVC-built, VS 2022 is
installed, and `lld-link` is present — target, LLVM ABI and linker all agree.
Unblocking gnu needs a gnu-ABI LLVM 18 (or an inkwell pin that admits a newer
LLVM) plus a single consistent mingw runtime; neither is a change this lane owns.

## Host note — a silent `gcc` caused by DLL shadowing

Before the link failure above, the seed build died in `ring`'s build script with
`gcc -E` returning 1 and **zero bytes of stderr**; `cc1.exe --version` printed
nothing and returned 0. Cause: `PATH` position 2 is `/mingw64/bin`, a DIFFERENT
msys2 root that ships no `gcc.exe` but does ship `libgmp-10.dll`, `zlib1.dll`,
`libzstd.dll` and `libwinpthread-1.dll`. `gcc` resolved from the real toolchain
at position 35 while its DLLs resolved from position 2, so `cc1.exe` loaded
mismatched support libraries and died mutely. Putting the real
`/c/dev/tool/msys2/mingw64/bin` first fixes it.

This is precisely what the plan's **W0 host-qualification** gate exists to catch
("tool discovery ... fail before cache use on an ABI/tool mismatch"). A W0 check
that compiled a two-line C file would have caught it in under a second instead of
after a full seed fingerprint plus a partial cargo build. W0 is not implemented.

## Reproduction

```sh
export LLVM_SYS_180_PREFIX=/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc
. scripts/check/lib/bootstrap-stage3/authority.shs
bootstrap_stage3_seed_inputs_fingerprint "$PWD" llvm "--features llvm" "$PATH" \
  x86_64-pc-windows-gnu; echo "RC=$?"
# before: RC=1, no output.   after: RC=0, fingerprint on stdout.
```

## References

- `scripts/check/lib/bootstrap-stage3/authority.shs`
- `scripts/bootstrap/bootstrap-from-scratch.sh` (`seed_inputs_hash`)
- `scripts/setup/platform-detect.shs`
- `doc/03_plan/compiler/windows_bootstrap_separate_hosts_nonconflicting_plan_2026-08-30.md`
