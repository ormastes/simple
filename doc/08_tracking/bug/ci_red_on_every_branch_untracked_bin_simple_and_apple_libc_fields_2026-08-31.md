# CI is red on every branch: untracked `bin/simple` + Apple/BSD `libc` field and variadic errors

**Date:** 2026-08-31
**Status:** FIXED (defects 1 and 2). Sibling multiplatform breaks filed separately —
see `ci_rust_bootstrap_multiplatform_all_lanes_red_2026-08-31.md`.
**Evidence run:** PR #148, head `21bf278fd7eeee85d6fc0558bac09f5bd85a9ef7`.

## Why this matters

`main`'s CI was red for every branch, so it gated nothing and no PR could ever
merge on a legitimately green run. Both defects below are **pre-existing on
`origin/main`** (`28ca075c2c76edc332e32913c89a13d664f9ad0d`) and are not caused
by PR #148, whose 11 commits touch zero files under `bin/` or `.github/`.

## Defect 1 — `bin/simple` is untracked, so `chmod +x bin/simple` always fails

Two jobs in **Windows Tests** (`.github/workflows/windows-tests.yml`) died
identically, immediately after checkout:

```
chmod: cannot access 'bin/simple': No such file or directory
Process completed with exit code 1
```

| job | id |
|---|---|
| Linker Tests | 99383294910 |
| Linux Validation | 99383295133 |

Run: <https://github.com/ormastes/simple/actions/runs/33357847195>

**Root cause.** `bin/simple` is not a tracked file. It is a symlink created
locally by `scripts/setup/setup.shs` (per `.claude/rules/commands.md`). A fresh
CI checkout can therefore never have it, and the step
`chmod +x bin/simple` — with no build before it — failed 100% of the time on
every branch including `main`.

**Pre-existence, verified directly:**

```
$ git cat-file -e 28ca075c2c7:bin/simple
fatal: path 'bin/simple' does not exist in '28ca075c2c7'      # NOT TRACKED on main
$ git cat-file blob 28ca075c2c7:.github/workflows/windows-tests.yml | grep -n 'chmod +x bin/simple'
46:        chmod +x bin/simple
145:        chmod +x bin/simple
```

**Fix.** Both jobs genuinely need a working binary — `linux-validation` runs
`simple test/ci/platform_linux.spl` and `simple test/ci/shell_exec.spl`;
`linker-tests` runs `simple build examples/hello.spl`. Deleting or guarding the
`chmod` would have produced a job that passes while testing nothing, i.e. a
fail-open. Each job now builds the bootstrap seed and deploys the symlink,
following the existing pattern in `containerized-tests.yml` and
`gpu-lane-tests.yml`, with a cargo cache so this does not add a cold ~10 min
build to every PR:

```yaml
- name: Build and deploy bin/simple (bootstrap seed)
  run: |
    cd src/compiler_rust
    cargo build --profile bootstrap -p simple-driver
    test -x target/bootstrap/simple
    cd "$GITHUB_WORKSPACE"
    mkdir -p bin
    ln -sfn "$(pwd)/src/compiler_rust/target/bootstrap/simple" bin/simple
    bin/simple --version
```

**Scan of all workflows.** `windows-tests.yml` lines 46 and 145 were the only
two occurrences of a bare `chmod +x bin/simple` at the PR head; both are fixed.
`build-binaries.yml` chmods `bin/simple_stage2`, which it builds itself in the
preceding step, so it is correct. `release.yml` has no such line at this tip.

**Related fail-open, NOT fixed here (out of scope, recorded deliberately).** In
the same file, jobs `windows-x64` and `windows-arm64` only `echo` — they print
`✗ No bootstrap runtime` and still exit 0, so they are green while asserting
nothing. `summary` likewise treats only `linux-validation` as critical. These
should either be made real or be removed; a green job that tests nothing is
worse than a red one.

## Defect 2 — Apple/BSD `libc` field names and variadic promotion

Job **Native — macOS aarch64** (99383303655), workflow **Rust Bootstrap
Multiplatform**, run <https://github.com/ormastes/simple/actions/runs/33357844564>.
Five errors, all in `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`:

```
error[E0609]: no field `st_mtimespec` on type `libc::stat`   file_io.rs:3102:31
error[E0609]: no field `st_mtimespec` on type `libc::stat`   file_io.rs:3102:61
error[E0609]: no field `st_ctimespec` on type `libc::stat`   file_io.rs:3103:31
error[E0609]: no field `st_ctimespec` on type `libc::stat`   file_io.rs:3103:61
error[E0617]: can't pass `u16` to variadic function          file_io.rs:326:56
error: could not compile `simple-compiler` (lib) due to 5 previous errors
```

This is the **second** macOS break. The first (`unresolved import objc2_metal` /
`dispatch2`) was fixed on PR #148 by re-gating `metal_graphics_runtime.rs` to
`all(target_os = "macos", feature = "metal")`; compilation then advanced far
enough to reveal these, which had been masked.

### Root cause 2a — `st_mtimespec` / `st_ctimespec` do not exist in the `libc` crate

`libc` is **vendored** in-tree at `src/compiler_rust/vendor/libc`, pinned to
`0.2.180` by `Cargo.lock`. Its Apple `stat` (`src/unix/bsd/apple/mod.rs:298`)
**flattens** Apple's native `timespec` fields and exposes them under the same
names Linux uses:

```rust
pub struct stat {
    ...
    pub st_mtime: time_t,
    pub st_mtime_nsec: c_long,
    pub st_ctime: time_t,
    pub st_ctime_nsec: c_long,
    ...
}
```

There is no `st_mtimespec`/`st_ctimespec` member at all, so the `#[cfg(target_os
= "macos")]` block could never have compiled. This is not a libc-version drift —
the fields are absent in the exact pinned, vendored source.

**Fix.** The macOS block was byte-identical in intent to the existing
linux/android one, so the two are merged and the macOS block deleted:

```rust
#[cfg(any(target_os = "linux", target_os = "android", target_os = "macos", target_os = "ios"))]
{
    ok = ok && before.st_mtime_nsec == after.st_mtime_nsec
            && before.st_ctime_nsec == after.st_ctime_nsec;
}
```

### Root cause 2b — `mode_t` is `u16` on Apple/BSD and cannot be passed variadically

`libc::open` is variadic. In C the third argument undergoes default argument
promotion to `int`/`unsigned int`; Rust instead rejects any sub-`int` type
(E0617). `libc::mode_t` is `u32` on Linux but **`u16` on macOS and FreeBSD**, so
`file_io.rs:326` compiled on Linux and failed on both.

**Fix** — promote explicitly, matching what C does implicitly:

```rust
let mode = args[2].as_int()? as libc::mode_t as libc::c_uint;
```

This is also **FreeBSD's only compile error** (job 99383303457,
`error[E0617]: can't pass u16 to variadic function`), so this one-line change
unblocks that lane too.

**Pre-existence, verified directly:**

```
$ git cat-file blob 28ca075c2c7:src/compiler_rust/compiler/src/interpreter_extern/file_io.rs | grep -n 'st_mtimespec\|st_ctimespec'
3102:                    && before.st_mtimespec.tv_nsec == after.st_mtimespec.tv_nsec
3103:                    && before.st_ctimespec.tv_nsec == after.st_ctimespec.tv_nsec;
$ ... | grep -n 'libc::open(path.as_ptr(), flags, mode)'
326:    let fd = unsafe { libc::open(path.as_ptr(), flags, mode) };
```

## How the fix was verified without a macOS host

No macOS machine was available. A full `cargo check -p simple-compiler --target
aarch64-apple-darwin` on this Linux host **fails inside `ring v0.17.14`'s C build
script** for lack of an Apple SDK, before ever reaching `simple-compiler`, so
that route proves nothing. (CI's real macOS runners have the SDK and did get
past `ring` — that is how these errors surfaced there.)

Instead an isolated probe crate depending on `libc =0.2.180` reproduced the exact
expressions from both sites. `cargo check` does not link, so no SDK is needed:

| target | pre-fix expressions | post-fix expressions |
|---|---|---|
| `aarch64-apple-darwin` | **4× E0609 + 1× E0617** (reproduces CI exactly) | PASS |
| `x86_64-apple-darwin` | — | PASS |
| `x86_64-unknown-freebsd` | — | PASS |
| `x86_64-unknown-linux-gnu` | — | PASS |

The pre-fix negative control is load-bearing: it proves the probe actually
discriminates rather than passing vacuously, and it reproduces CI's error set
byte-for-byte (same codes, same count). The real crate additionally still
compiles on the Linux host (`cargo check --release -p simple-compiler`,
`Finished` clean).

**What remains unproven:** no full-crate compile or test run on a real macOS or
FreeBSD host was performed. The evidence covers type-checking of the changed
expressions only. Both changed sites are on a path that is inert on non-Linux
anyway (`fd = -1` under `#[cfg(not(target_os = "linux"))]` in the
`st_*_nsec` function), so the change needs to compile, not to alter behavior.

## Guard gap

`scripts/check/check-seed-builds-push.shs` runs `cargo check --release --bin
simple` for the **host target only**. Every defect above is invisible to it:
defect 1 is a workflow/infra break it never looks at, and defect 2 lives behind
`#[cfg(target_os = ...)]` arms that the host build never instantiates. This is
precisely why macOS- and BSD-only breaks reach `main` with all guards green.

**Recommendation:** extend that guard with `cargo check --target
aarch64-apple-darwin` (and `x86_64-unknown-freebsd`, `x86_64-pc-windows-msvc`)
for the crates that compile without a platform SDK, or add a cheap
`cargo check`-only cross lane. A full cross-check is blocked by `ring`'s build
script; a scoped check of the `#[cfg]`-heavy modules is not, as demonstrated
above. Filed as the concrete follow-up in the sibling record.
