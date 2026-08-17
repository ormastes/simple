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

## Can we switch to LLVM 20 today? No — measured 2026-08-17

Asked directly, and answered by reading the binding rather than the shell. The
answer is **no, and the one-line change is actively dangerous**. Four facts, each
verified in this tree:

1. **How LLVM is actually linked.** Two independent mechanisms, not one.
   - *Rust seed, static:* `src/compiler_rust/compiler/Cargo.toml:105` —
     `inkwell = { version = "0.5", optional = true, features = ["llvm18-0"] }`,
     behind the optional `llvm` feature (`:18`, `default = []` at `:16`).
     `bootstrap-from-scratch.sh:1207` turns it on (`llvm_features="--features llvm"`)
     whenever `backend` is `llvm`/`llvm-lib`, and `:131` sets `backend="llvm"`,
     so the seed **does** link LLVM on the default path. `inkwell` pulls
     `llvm-sys 180.0.0` (`src/compiler_rust/Cargo.lock:2375-2377`).
   - *Pure-Simple side, dynamic:* `src/lib/nogc_sync_mut/sffi/llvm_loader.spl:52-72`
     `dlopen`s a hardcoded candidate list — `libLLVM-18.so`, `-17`, `-19`.
     **There is no `libLLVM-20.so` entry.** `SIMPLE_LLVM_PATH` (exported by
     `platform-detect.shs:167`) overrides the list and is tried first.
     This is the "Pure-Simple mode: dynload" the bootstrap log refers to.
2. **inkwell 0.5 cannot target LLVM 20 at all.** The vendored crate's highest
   feature is `llvm18-0` (`src/compiler_rust/vendor/inkwell/Cargo.toml`, no
   `llvm19-*` or `llvm20-*` exists). LLVM 20 needs inkwell >= 0.6 and
   `llvm-sys 200.x`.
3. **The build is hermetic, so the crate bump is not a `cargo update`.**
   `src/compiler_rust/.cargo/config.toml` replaces crates-io with
   `directory = "vendor"`, and every bootstrap `cargo build` passes
   `--locked --offline` (`bootstrap-from-scratch.sh:1481-1504`). `vendor/`
   contains only `llvm-sys 180.0.0` and `inkwell 0.5.0`. Switching majors
   therefore requires a networked `cargo vendor --respect-source-config` refresh
   **and** committing the new vendored trees — a deliberate dependency change,
   not a configuration tweak.
4. **The naive change fails silently rather than loudly — this is the trap.**
   Setting `LLVM_VERSIONS="20 18"` works on the shell side: detection selects
   `/usr/lib/llvm-20`, exports `LLVM_SYS_200_PREFIX` and
   `SIMPLE_LLVM_PATH=/usr/lib/llvm-20/lib/libLLVM-20.so` (verified). But
   `llvm-sys 180`'s `build.rs` reads only `LLVM_SYS_180_PREFIX`, which is now
   **unset**, so it falls back to `llvm-config` on `PATH` — which is 18 here —
   and links 18 anyway. Result: one process statically linked against LLVM 18
   while its `dlopen` path points at LLVM 20, with no error at any stage. The
   earlier note above ("produces a link failure, not a fallback") was optimistic:
   on *this* host the failure mode is a silent split-brain, because a compatible
   `llvm-config` happens to be on `PATH`.

**Consequence:** `LLVM_VERSIONS` was left at `18`. It is a correct pin, not an
oversight, and the comment at `platform-detect.shs:54-56` already says so.

### Prerequisites for an actual LLVM 20 migration

All four must land together; any subset produces the split-brain above:

- `cargo vendor` refresh bringing in `inkwell >= 0.6` + `llvm-sys 200.x`
  (requires network; `vendor/` is committed).
- `compiler/Cargo.toml:105` feature `llvm18-0` -> `llvm20-1`, and any inkwell
  0.5 -> 0.6 API breakage fixed in `src/compiler_rust/`.
- `llvm_loader.spl:52-72` (and its `ffi/` twin) gaining `libLLVM-20.so` /
  `libLLVM-20.so.1` candidates.
- `LLVM_VERSIONS` default -> `"20 18"` **last**, so the pin degrades gracefully
  on hosts without 20.

### Guard

`scripts/check/check-llvm-toolchain-consistency.shs` makes this class of drift
fail-closed instead of silent. It cross-checks the `LLVM_VERSIONS` default, the
inkwell `llvmNN-0` feature, the `llvm-sys` major in `Cargo.lock`, the highest
feature the *vendored* inkwell can supply, and the `libLLVM-<major>.so`
candidates in `llvm_loader.spl`. Verdict is the last stdout line
(`PASS`/`FAIL` exit 1/`ERROR` exit 2, zero invariants checked is always ERROR);
`--selftest` is fatal and runs 7 fixtures before any real scan, including a
consistent LLVM 20 tree that must PASS — the guard blocks *inconsistency*, never
forward movement.

```
$ sh scripts/check/check-llvm-toolchain-consistency.shs
PASS — 5 invariant(s) checked, LLVM toolchain consistent (pref=[18] inkwell=llvm18-0 llvm-sys=18 vendor-max=llvm18)

$ sh scripts/check/check-llvm-toolchain-consistency.shs --root <tree with LLVM_VERSIONS="20 18">
FAIL — 5 invariant(s) checked ...: shell prefers LLVM 20 but inkwell is pinned to
llvm18-0 (llvm-sys would silently link 18 via PATH llvm-config while
SIMPLE_LLVM_PATH points at 20); LLVM_VERSIONS lists major 20 but llvm_loader.spl
has no libLLVM-20.so candidate
```
