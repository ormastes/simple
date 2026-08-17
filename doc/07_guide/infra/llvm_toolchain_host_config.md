# LLVM toolchain: what this host has, and how the version is chosen

Probed 2026-08-17 on the primary dev host (`x86_64-unknown-linux-gnu`).

## Installed on this host

| prefix | version | `clang` |
|---|---|---|
| `/usr/lib/llvm-18` | 18.1.8 | `clang-18` 18.1.8 |
| `/usr/lib/llvm-20` | 20.1.8 | `clang-20` 20.1.8, and bare `clang` -> 20.1.8 |

Nothing else is installed. There is no LLVM 21, 22, 23, or 32 on this host, and
no such prefix exists under `/opt`. LLVM's current release series is 20.x, so a
`23.x` or `32.x` toolchain cannot be installed today — a request for one is a
request for a future release, not a configuration change.

Note the mismatch worth knowing about: bare `clang` resolves to **20**, while
bare `llvm-config` resolves to **18**. Anything that shells out to `clang`
without a version suffix is using a different major version than the bootstrap
links against.

## How the bootstrap picks a version

`scripts/setup/platform-detect.shs:64`

```sh
: "${LLVM_VERSIONS:=18}"
```

`LLVM_VERSIONS` is a **preference-order list of major versions**, first match
wins (`platform-detect.shs:54-63`, loop at `:135`). The default is the single
entry `18`, which is why a host with both 18 and 20 installed still reports:

```
LLVM 18 found: /usr/lib/llvm-18 (lib: /usr/lib/llvm-18/lib/libLLVM-18.so)
```

20.1.8 is present and simply never considered. This is a pin, not a detection
failure.

## Selecting LLVM 20

No code change is required — the override already exists:

```sh
LLVM_VERSIONS="20 18" sh scripts/bootstrap/bootstrap-from-scratch.sh   # prefer 20, fall back to 18
LLVM_VERSIONS=20      sh scripts/bootstrap/bootstrap-from-scratch.sh   # 20 only, fail if absent
```

`platform-detect.shs:166` derives `LLVM_SYS_<major>0_PREFIX` from whichever
version is selected, so the Rust `llvm-sys` linkage follows automatically.

## Before changing the default to 20

The default pin is **not** obviously wrong, and flipping it is a real change,
not a cleanup. Check all of these first:

- **`llvm-sys` crate compatibility.** The Rust seed links LLVM through
  `llvm-sys`, whose crate version must match the LLVM major. Bumping the
  toolchain without bumping the crate produces a link failure, not a fallback.
- **Cache invalidation.** `object_cache_key` folds the compiler fingerprint,
  backend, opt-level, CPU and SIMD tier; a toolchain change invalidates native
  build caches, so the first build after the switch is cold.
- **The bootstrap must be idle.** Changing the toolchain under a running
  bootstrap mixes artifacts across majors.

## Verifying, rather than assuming

```sh
ls -d /usr/lib/llvm-*                      # what is actually installed
llvm-config --version; clang --version     # note: these can disagree (18 vs 20 here)
grep -n 'LLVM_VERSIONS' scripts/setup/platform-detect.shs
```

Read the bootstrap's own `LLVM <n> found:` line to confirm which prefix a given
run selected — that line is authoritative for that run, and is the only thing
that proves which toolchain produced a binary.
