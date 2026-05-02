# Userland Port — Tier C Deferred Packages

**Origin:** `/dev port-userland-to-simpleos` on 2026-04-24. User supplied a 40-package Ubuntu bash install script. Tier A1 (26 existing shell builtins) and Tier A2 (tree, less — new this run) + Tier B (7 aliases) landed in the same /dev run. The packages below are explicitly **deferred** with concrete rationale.

**Status:** not-started. Each row becomes its own `/dev` run when the repo is ready.

## Deferred heavyweight ports (from original Tier A, moved out after Phase 2 research)

| Package | Reason deferred |
|---------|-----------------|
| `tar` | ustar/pax streaming format; multi-KLOC real port. Needs `[u8]` buffer strategy per memory `feedback_interpreter_bulk_buffer.md`. |
| `xz` | LZMA2 decoder is multi-KLOC in every reference impl (liblzma, xz-embedded). Requires big-buffer strategy. |
| `unzip` | ZIP local+central directory walker + DEFLATE. |
| `zip` | DEFLATE encoder + ZIP writer. Pair with `unzip`. |
| `jq` | Full JSON parser + path/filter language (regex, reductions, pipes). Larger than `awk` port. |

## Deferred external-subsystem ports (from original Tier C)

| Package | Reason deferred |
|---------|-----------------|
| `curl` | Requires net stack + TLS client + multi-protocol support. |
| `wget` | Overlaps `curl`; do together. |
| `htop` | Requires procfs + top-style TUI with cursor control. |
| `lsof` | Requires kernel fd-tracking exposure. |
| `strace` | Requires kernel syscall tracing hook. |
| `net-tools` | `ifconfig`/`route`/`arp` — each needs net stack exposure. |
| `procps` | `ps` exists; `top`, `vmstat`, `iostat` need procfs counters. |
| `psmisc` | `killall`, `pstree`, `fuser` — minor surface; bundle with `ps` work. |

## Deferred toolchain ports (from original Tier C)

| Package | Reason deferred |
|---------|-----------------|
| `make` | POSIX Make + dependency graph engine. |
| `cmake` | Multi-KLOC C++ project; we already have `/usr/bin/cmake` wrapper shim per `os_shell_spec.spl`. A real port is separate work. |
| `ninja-build` | Similar to `cmake`; wrapper exists. |
| `clang` | LLVM frontend — out-of-scope as a Simple port. Wrapper shim covers basic version/flag queries. |
| `lld` | Replaced by `mold` in our rootfs (landed 2026-04-24). Formal lld port not required. |
| `pkgconf` | Short port (~few KLOC); feasible but not requested this run. |
| `python3` | A Python interpreter port to Simple is a multi-month effort of its own. |
| `python3-pip` | Follows `python3`. |

## Deferred small ports & wrappers

| Package | Reason deferred |
|---------|-----------------|
| `yq` | Same complexity class as `jq`; treat together. |
| `p7zip-full` | Combines multiple codecs (LZMA, LZMA2, bzip2, gzip). Do after tar/xz. |
| `fzf` | Fuzzy-matcher TUI; small algorithmic port but needs interactive terminal abstraction. |
| `shellcheck` | Haskell project in upstream; rewrite-from-scratch scope. |
| `universal-ctags` | Language-aware symbol indexer; multi-KLOC. |

## Already covered

| Package | Covered by |
|---------|-----------|
| `bash` (as script interpreter) | `src/os/apps/shell/` + bash-compat commit `8c7eb470f3`. Full `bash` upstream parity is out of scope. |
| `coreutils` (GNU) | 26 shell builtins already + tree/less added 2026-04-24. |
| `findutils` (find) | `tool_find` in shell. |
| `grep`, `sed`, `gawk` | `tool_grep`, `tool_sed`, `tool_awk` in shell. |
| `git` | `src/os/apps/git/` exists. |
| `diffutils` (diff, patch) | `tool_diff`, `tool_patch` in shell. |
| `procps` (`ps`) | Partial — `tool_ps` exists. `top`/`vmstat` deferred. |
| `silversearcher-ag` | Alias `ag→grep` landed 2026-04-24. |
| `ripgrep` | Alias `rg→grep` landed 2026-04-24. |
| `fd-find` | Alias `fd→find` + `fdfind→find` landed 2026-04-24. |
| `bat` | Alias `bat→cat` + `batcat→cat` landed 2026-04-24. |
| `eza` | Alias `eza→ls` landed 2026-04-24. |
