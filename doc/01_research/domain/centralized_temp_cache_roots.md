<!-- codex-research -->

# Centralized Temporary and Cache Roots

**Status:** Domain research  
**Date:** 2026-09-03  
**Scope:** Current primary-source policies and a two-root mapping for Simple

## Executive Recommendation

Simple should expose exactly two authoritative filesystem roots:

| Variable | Default | Lifetime and contents |
|---|---|---|
| `SIMPLE_USER_ROOT` | macOS: `~/Library/Caches/simple`; Linux: `${XDG_CACHE_HOME:-$HOME/.cache}/simple` | User-owned, cross-worktree, discardable storage: content-addressed caches, downloaded toolchains, schema/codegen caches, retained logs, and cache-local publication staging. |
| `SIMPLE_WORKTREE_ROOT` | `<canonical-worktree>/.simple` | Worktree-isolated ephemeral/build state: sessions, process scratch, locks, sockets, test runs, generated build trees, and convenience links or receipts that identify user-cache artifacts. |

All Simple-owned temporary and cache directories must be descendants of one of these roots. The two variables must be absolute after resolution. A command may override either root explicitly, but must not create a third implicit root from `TMPDIR`, `/tmp`, the current directory, or a tool-specific default.

Recommended internal layout:

```text
$SIMPLE_USER_ROOT/
  cache/
    cas/v1/<algorithm>/<prefix>/<digest>
    compiler/<compiler-identity>/
    packages/
    schemas/
    tools/
  staging/                 # same-filesystem cache publication only
  locks/
  logs/
  gc/

$SIMPLE_WORKTREE_ROOT/
  tmp/<command>/<session-id>/
  build/<profile>/<target>/
  test/<run-id>/
  ipc/<session-id>/
  locks/
  receipts/
```

The resolver should export tool-specific variables to child processes instead of allowing each tool to choose another location:

```text
TMPDIR              = $SIMPLE_WORKTREE_ROOT/tmp/<command>/<session-id>
GOTMPDIR            = same session directory
GOCACHE             = $SIMPLE_USER_ROOT/cache/go-build
CARGO_HOME          = $SIMPLE_USER_ROOT/cache/cargo/home
CARGO_TARGET_DIR    = $SIMPLE_WORKTREE_ROOT/build/cargo/<profile-target-key>
PYTHONPYCACHEPREFIX = $SIMPLE_USER_ROOT/cache/python/pycache/<python-identity>
```

## Comparative Findings

### Go

Go separates short-lived work from reusable build cache. `GOTMPDIR` controls temporary sources, packages, and binaries; `GOCACHE` controls reusable build outputs and must be absolute. The cache is designed for concurrent invocations, keys relevant compiler inputs, periodically removes old entries, and supports explicit cleanup. Go also keeps downloaded modules separately in `GOMODCACHE`. This is strong precedent for distinct scratch and reusable-cache namespaces, with an application-owned resolver projecting standardized variables. [Go command environment and build-cache documentation](https://go.dev/cmd/go/?m=old), [Go `GOTMPDIR` behavior test](https://go.dev/src/cmd/go/testdata/script/build_GOTMPDIR.txt), [Go installation/cache management](https://go.dev/doc/manage-install)

### Rust and Cargo

Cargo separates the shared download/source cache in `CARGO_HOME` from workspace build products in `target-dir`. `CARGO_TARGET_DIR`, `build.target-dir`, or `--target-dir` can relocate outputs. Current Cargo additionally supports a separate intermediate `build-dir` and path templates including `{workspace-root}`, `{cargo-cache-home}`, and `{workspace-path-hash}`. Cargo does not define a dedicated universal scratch variable; Rust's standard `temp_dir()` follows `TMPDIR` on Unix, Apple's per-user temp directory on Darwin, and `/tmp` on other Unix systems, while warning that temporary locations may be shared and names must be created securely. Simple should therefore project Cargo's persistent and build paths separately and project `TMPDIR` for subprocess scratch. [Cargo environment variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html), [Cargo configuration](https://doc.rust-lang.org/cargo/reference/config.html), [Cargo build cache](https://doc.rust-lang.org/stable/cargo/reference/build-cache.html), [Rust `std::env::temp_dir`](https://doc.rust-lang.org/std/env/fn.temp_dir.html)

### XDG Base Directory

XDG assigns user-specific, nonessential reusable data to `XDG_CACHE_HOME`, defaulting to `$HOME/.cache`. It reserves `XDG_RUNTIME_DIR` for small runtime communication objects; that directory must be user-owned, mode `0700`, local, fully featured, and tied to the login lifetime. XDG explicitly warns against putting large files in the runtime directory. Simple should use the XDG cache default on Linux, but should not make `XDG_RUNTIME_DIR` a third storage root. If interoperability requires a socket there, create only a short indirection or endpoint and keep bulk state beneath `SIMPLE_WORKTREE_ROOT`. [XDG Base Directory Specification 0.8](https://specifications.freedesktop.org/basedir/0.8/)

### Python

Python's `tempfile` searches `TMPDIR`, `TEMP`, and `TMP`, then platform locations, and finally the current directory. Its high-level APIs securely generate unpredictable names and provide automatic cleanup; low-level APIs require callers to clean up. This flexible fallback is useful for a general library but conflicts with Simple's cleanup objective, so Simple should always pass an explicit directory or export a resolved `TMPDIR`. Python bytecode caches can be redirected with `PYTHONPYCACHEPREFIX`, avoiding `__pycache__` proliferation throughout source trees. [Python `tempfile`](https://docs.python.org/3/library/tempfile.html), [Python `sys.pycache_prefix`](https://docs.python.org/3/library/sys.html#sys.pycache_prefix)

### CMake

CMake distinguishes the source tree from a dedicated binary/build tree selected with `-B`; `CMakeCache.txt` identifies and persists configuration in that build tree. CMake strongly encourages out-of-source builds because they keep source clean, allow multiple configurations, and make generated state easy to remove. CMake does not provide one global content cache equivalent to `GOCACHE`. Simple should invoke CMake with `-B $SIMPLE_WORKTREE_ROOT/build/cmake/<configuration-key>` and place any external compiler cache under the user root. [CMake command manual](https://cmake.org/cmake/help/latest/manual/cmake.1.html), [CMake directory-structure guidance](https://cmake.org/cmake/help/book/mastering-cmake/chapter/Getting%20Started.html), [CMake cache guidance](https://cmake.org/cmake/help/book/mastering-cmake/chapter/CMake%20Cache.html)

### Bazel

Bazel's design goals closely match Simple's: avoid collisions between users, workspaces, configurations, and tools; keep all per-user build state under one directory; and support selective cleanup. Bazel defaults its output root to the OS user-cache location, creates a per-user root, identifies installations by manifest hash, and identifies each workspace output base by a hash of the canonical workspace path. This supports a shared user root while preserving worktree identity. Simple should adopt the identity strategy, but retain worktree-local ephemeral state as its second visible root. [Bazel output-directory layout](https://bazel.build/remote/output-directories)

### macOS

Apple distinguishes temporary data, which is not required across launches and should be deleted promptly, from reproducible cache data under `~/Library/Caches/<application>`. Apple recommends resolving these locations through platform APIs because sandboxed and nonsandboxed locations differ. Rust likewise uses Darwin's `_CS_DARWIN_USER_TEMP_DIR` when `TMPDIR` is absent. Simple's macOS default should therefore be `~/Library/Caches/simple` for the user root, while worktree scratch remains in `.simple` so cleanup and ownership are explicit. System-provided temporary paths may be used only as a bootstrap fallback before a worktree is known, and must be migrated or deleted once resolution completes. [Apple filesystem-use guidance](https://developer.apple.com/documentation/foundation/using-the-file-system-effectively), [Apple macOS Library directory guidance](https://developer.apple.com/library/archive/documentation/FileManagement/Conceptual/FileSystemProgrammingGuide/MacOSXDirectories/MacOSXDirectories.html), [Rust Darwin temp resolution](https://doc.rust-lang.org/std/env/fn.temp_dir.html)

### Linux

Linux systems commonly clean `/tmp` through administrator policy, while `/var/tmp` is intended to survive reboots. `systemd-tmpfiles` confirms that files in `/tmp` may be subject to system-wide age-based cleanup even when user cleanup policy differs. XDG cache storage is therefore the appropriate persistent, user-owned default; worktree-local scratch avoids unpredictable global cleanup during an active build. [Filesystem Hierarchy Standard: `/var/tmp`](https://specifications.freedesktop.org/fhs/latest/varTmp.html), [`systemd-tmpfiles`](https://www.freedesktop.org/software/systemd/man/systemd-tmpfiles.html)

## Design Consequences

### Ownership and security

- Resolve both roots without following an attacker-controlled final symlink; canonicalize the worktree before deriving its identity.
- Reject relative roots, roots owned by another user, and writable parent chains that violate the selected trust profile.
- Create private session, staging, lock, and IPC directories with mode `0700`; create files atomically with exclusive creation and unpredictable names.
- Never trust a predictable filename under a shared temporary directory. Rust and Python both explicitly warn or provide secure primitives for this case.
- Do not share mutable cache entries. Publish immutable objects by digest, and keep mutable metadata behind locks or compare-and-swap records.
- Credentials and irreplaceable state do not belong in either root; both roots are discardable.

### Cleanup policy

- `simple clean --worktree` removes only descendants of the current canonical `$SIMPLE_WORKTREE_ROOT` after validating its root marker.
- `simple clean --user-cache` removes selected namespaces under `$SIMPLE_USER_ROOT/cache`; default behavior is age/size eviction, not unconditional deletion.
- Session directories carry owner PID, process-start identity, creation time, command, and worktree digest. Cleanup removes terminal sessions immediately and stale sessions after a policy delay.
- Cache entries carry last-access or generation metadata and may be recreated. The cleaner uses a lock/lease before deletion and supports dry-run output.
- Cleanup never traverses symlinks and never accepts an empty, `/`, home-directory, or worktree path as a recursive deletion target.

### Atomic publication and filesystem boundaries

POSIX `rename` atomically replaces a destination on the same mounted filesystem, but fails with `EXDEV` across mounts. Therefore cache production must write and fsync a temporary object beneath `$SIMPLE_USER_ROOT/staging/<destination-shard>` and rename it into `$SIMPLE_USER_ROOT/cache`; it must not stage in the worktree root and assume rename remains atomic. Worktree artifacts follow the same rule within `$SIMPLE_WORKTREE_ROOT`. Cross-root promotion is copy-and-verify into destination-local staging, followed by destination-local atomic rename. [Linux/POSIX `rename(2)` semantics](https://www.man7.org/linux/man-pages/man2/rename.2.html)

### Path length

- Keep both configured roots short and absolute. Do not embed full source paths, package names, command lines, or nested dependency trees in physical cache paths.
- Use fixed-width digests for worktree, toolchain, configuration, and content identity; retain readable names in metadata and receipts.
- Limit human-readable path components to sanitized bounded prefixes and reserve headroom for compiler/linker suffixes.
- Detect path-length failure before invoking downstream tools and report the resolved root and offending logical component.
- Bazel's hashed workspace output base demonstrates the value of stable, bounded workspace identities.

### Per-worktree isolation and sharing

- Compute `worktree_id = H(canonical repository identity, canonical worktree path)` and store it in `$SIMPLE_WORKTREE_ROOT/root.sdn`.
- Never share mutable build trees, sessions, locks, sockets, or test output across worktrees.
- Share only immutable or concurrency-safe content-addressed user-cache objects.
- Include compiler, schema, target, profile, relevant environment, and input digests in cache keys; a path hash alone is an isolation key, not a correctness key.
- Convenience links in the worktree may point into the user cache, but deletion tools operate on the authoritative roots rather than following those links.

## Resolution Precedence

1. Explicit command-line root override.
2. `SIMPLE_USER_ROOT` or `SIMPLE_WORKTREE_ROOT` environment variable.
3. Platform default for the user root and `<canonical-worktree>/.simple` for the worktree root.
4. If no worktree exists, create a command-scoped directory at `$SIMPLE_USER_ROOT/tmp/no-worktree/<session-id>`; this remains inside the user root and does not introduce a third root.

Legacy variables such as `TMPDIR`, `GOTMPDIR`, `GOCACHE`, `CARGO_HOME`, and `CARGO_TARGET_DIR` are inputs only for an explicit compatibility mode. In normal Simple-owned execution, KPF/tooling/build launchers overwrite them for children with projections of the two resolved roots and record the projection in the execution receipt.

## Recommended Policy

Adopt the two roots above as the only Simple storage authorities. Use the user root for reusable, immutable, discardable data and destination-local cache staging. Use the worktree root for mutable and short-lived state whose ownership and cleanup follow one checkout. Centralize resolution in one library and one launcher projection, make all roots visible through `simple env --paths`, require receipts to record effective roots, and reject silent fallback to any third directory.
