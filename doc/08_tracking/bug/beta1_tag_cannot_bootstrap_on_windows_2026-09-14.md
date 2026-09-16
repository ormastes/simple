# The v1.0.1-beta.1 tag cannot bootstrap on Windows
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-09-14
**Impact:** the beta 1 GitHub release has carried **zero assets since 2026-09-06**, and
no pure-Simple Windows binary has ever been produced from that commit.
**Status:** root cause identified; already fixed on `main`, NOT in the tag.

## Root cause

`bootstrap_stage3_verify_hosted_runtime_authority`
(`scripts/check/lib/bootstrap-stage3/authority.shs`) required the hosted root
directory to have mode **exactly 0500**:

```perl
@st && !S_ISLNK($st[2]) && S_ISDIR($st[2]) &&
    S_IMODE($st[2]) == oct("0500") or exit 1;
```

Measured on this host:

```
chmod 500 <dir>  ->  perl lstat reports 0755
```

On MSYS/Windows `chmod` on a *directory* is a no-op, so that comparison can
never be true and the check fails **every** bootstrap. The failure surfaces far
away as:

```
error: could not prepare immutable Rust authority generation
```

with no indication of which branch failed, because the whole call chain returns
bare `1`/`64`.

## Already fixed on main, after the tag

`origin/main` carries the relaxation, and the sibling walk in the same function
documents exactly why:

> Windows cannot represent these modes: MSYS reports 0444 for any read-only
> file (losing both the owner-only narrowing and the execute bit) and **ignores
> the freeze on directories entirely, leaving them 0755**. Measured on a frozen
> staging tree. Assert what IS representable … and do not claim directory
> immutability the platform cannot provide.

The 0500 directory branch was simply missed when that handling was added, and
the fix landed after `v1.0.1-beta.1` was cut. So the tag is structurally
unbuildable on Windows while current `main` is fine.

## How it was found

The call chain returns unlabelled status codes, so three instrumentation passes
were needed, each adding one `echo` per failure branch:

1. `bootstrap_stage3_prepare_seed_generation` -> `PREPGEN-FAIL-4`
2. `bootstrap_stage3_copy_seed_tuple` -> no marker fired; its LAST statement has
   no `|| return`, so its status is the implicit return value
3. `bootstrap_stage3_verify_hosted_runtime_authority` -> `HOSTAUTH-FAIL-21`

Each pass cost a full seed rebuild. See the companion change adding those
diagnostics permanently.

## Consequences for releasing beta 1

Building beta 1 on Windows requires backporting this fix to the release line,
which by `doc/07_guide/infra/software_release.md` means a **new identity**
(`beta.2`) -- a published tag is never re-cut.

Building it on Linux/macOS is the intended path and needs no backport. Note
every prior release shipped POSIX assets only: `v0.9.8` linux-x86_64, `v0.9.6`
linux-x86_64 + darwin-arm64. **No release has ever shipped a Windows asset.**

A WSL attempt on this host got as far as the seed build and stopped on an
unrelated environment limit: cargo 1.75 against a lockfile that declares
version 4 (needs >= 1.78).

## Other Windows gaps hit on the way, recorded so they are not rediscovered

- A worktree root of 39 characters made MSVC fail with
  `C1083: cannot open compiler generated file ''`. The same build at a 6-char
  root succeeded. Deep `rust-authority-<64hex>/target/...` paths leave very
  little headroom under MAX_PATH.
- After the authority fix, Stage 2 reached `seed -> bootstrap_main.spl` and
  stopped at `could not write command transcript`; creating
  `<output>/stage3/<platform>/` by hand did not clear it, so `output_dir`
  resolves somewhere else. Unreached and undiagnosed.

## Correction 2026-09-14: CI DID build a Windows binary from this tag

The **Impact** line above says no pure-Simple Windows binary has ever been
produced from this commit. That is wrong, and the evidence is the tag's own
release run `34067963746`:

| leg | result |
|---|---|
| linux-x86_64, linux-aarch64, linux-riscv64 | success |
| windows-x86_64, windows-aarch64 | **success** |
| freebsd-x86_64 | success |
| darwin-arm64, darwin-x86_64, freebsd-x86 | failure |
| SimpleOS x86_64 Kernel Build | failure |

Seven `bootstrap-*` artifacts plus `installers` (116 MB) were produced and are
still unexpired. So the tag is buildable on Windows *through the CI lane*. What
is broken is the local `bootstrap-from-scratch.sh` lane on an MSYS host, which
is exactly what the 0500 directory-mode root cause above describes. The scope of
this record is that lane, not the tag as a whole.

## Why the release has zero assets — it is NOT this bug

`create-release` is gated `needs.whole-tests.result == 'success'`, and
`whole-tests` is gated `needs.build-bootstrap.result == 'success'`. The matrix
declares no `continue-on-error`, so the three failed legs made `build-bootstrap`
fail, which **skipped** `whole-tests`, which **skipped** `create-release`.
`Create GitHub Release` never failed — it never ran.

The blocker for shipping beta 1 is therefore the darwin x2 + freebsd-x86 legs,
not the Windows bootstrap defect. `origin/main`'s workflow is *stricter* (it
additionally requires `build-installers` and `simpleos-build` to succeed), so
re-cutting as beta.2 from main does not relax this gate.

## WSL local-build lane: how far it actually gets

The earlier note "cargo 1.75 against a lockfile that declares version 4 (needs
>= 1.78)" understated the requirement and overstated the blocker.

- cargo/rustc **1.82** are obtainable rootless on jammy: `apt-get download` into
  a private `Dir::State::Lists`/`Dir::Cache`, then `dpkg-deb -x` into `$HOME`
  (the same pattern used for the LLVM 23 deploy). Verified working.
- 1.82 is still not enough. The vendored `jni-0.22.4` manifest requires
  `edition2024`, stabilised in Rust **1.85**:
  `feature 'edition2024' is required ... not stabilized in this version of Cargo`.
- questing ships cargo 1.85.1, but its binaries link `GLIBC_2.38` while jammy
  provides 2.35, so the rootless-extract trick does not carry across that gap.

So the WSL lane needs a host glibc newer than Ubuntu 22.04's, or a rustup-style
static toolchain — not merely a newer apt pocket.

