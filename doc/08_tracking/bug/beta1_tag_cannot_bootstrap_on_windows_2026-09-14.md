# The v1.0.1-beta.1 tag cannot bootstrap on Windows

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
