# msys2 sh drops environment variables inherited from Git Bash parents

Date: 2026-10-15
Host: Windows 11, Git Bash (`C:\dev\tool\Git`), MSYS2 at `C:\dev\tool\msys2`
Symptom class: child `sh` processes lose exported/inline environment
variables; config silently reverts to defaults or "not found".

## Observation

`C:\dev\tool\msys2\usr\bin\sh.exe` (and bash.exe), when spawned from a Git
Bash process, starts with a scrubbed environment: only `MSYSTEM`, `PATH`,
`SYSTEMDRIVE`, `SYSTEMROOT`, `WINDIR`, `TERM`, `HOME` survive (7 of 69
vars observed). Both inline prefix assignments
(`FOO=bar sh -c ...`) and parent-`export`ed variables are dropped. The same
binary spawned from an msys2 parent passes environment normally
(`FOO=inner sh -c 'echo $FOO'` works nested).

Consequence: after `scripts/setup/host-env.shs` `host_env_apply_path`
prepends msys2 paths onto PATH (this host's `SIMPLE_HOST_PATH_PREPEND`
includes `C:\dev\tool\msys2\usr\bin`), every bare `sh` child resolves to
the msys2 build and inherits a nearly empty environment.

Manifestations hit while bringing up the release_phase3 Windows bootstrap:

- `SIMPLE_BOOTSTRAP_BUILD_ROOT=... sh scripts/setup/materialize-symlinks-windows.shs ...`
  silently behaves as if the variable were unset (guard falls back to the
  default dedicated root; the receipt is then refused).
- Any `VAR=value sh helper.shs` pattern in tests or tooling after host-env
  is sourced.

The canonical bootstrap flow is mostly immune because it runs under one
long-lived shell and re-exports inside it, but any subprocess that re-execs
`sh` through the msys2 binary loses the exported config.

## Workarounds

1. Prefer `export` + invoke through Git Bash's own `/usr/bin/sh` (absolute
   path), or keep `sh` resolving to Git Bash by not letting msys2 paths
   shadow it for the invocation.
2. For msys2→msys2 chains, set variables inside the msys2 parent shell:
   `sh -c 'export VAR="$1"; shift; exec sh "$@"' _ value ...` — env passing
   works between msys2 processes.
3. Detection one-liner for a host:

   `FOO=probe "$(command -v sh)" -c 'echo "${FOO:-MISSING}"'`

   If it prints MISSING and `command -v sh` lives under an MSYS2 root, this
   host is affected.

## Suggested direction

`host_env_apply_path` prepends `SIMPLE_HOST_PATH_PREPEND` wholesale. On
Git Bash hosts, POSIX-tool entries from a foreign msys2 root (sh, bash,
env, coreutils) should either be excluded or shadowed by Git Bash's own
`/usr/bin`, so config-bearing child shells keep Git Bash's environment
semantics. Needs care: some entries (perl, clang) may be intentionally
msys2-provided.

## Status (2026-10-16): fixed for DESKTOP-VMF96U6 via host config

`config/host/DESKTOP-VMF96U6.sdn` now lists Git Bash's own `/usr/bin` ahead
of `/c/dev/tool/msys2/usr/bin`. After `host_env_apply_path`: `sh`, `bash`,
`env` resolve to `/usr/bin/*` and the detection one-liner prints `probe`
(before: `/c/dev/tool/msys2/usr/bin/sh`, `MISSING`). msys2 still provides
tools Git Bash lacks. Other Windows hosts with an msys2 `usr/bin` prepend
need the same ordering.
