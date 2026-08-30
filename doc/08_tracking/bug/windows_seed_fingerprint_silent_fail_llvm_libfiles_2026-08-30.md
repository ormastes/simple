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
