# Native directory walk runtime parity

Status: Fixed and owner-tested; pure-Simple source spec pending an admitted runtime.
 
 Date: 2026-07-16
 
 ## Problem
 
 `dir_walk_native` is the canonical shell-free recursive file walker, but its
 runtime implementations disagree:
 
 - the C runtime returns non-directory entries and follows directory symlinks
   because it classifies paths with `stat`;
 - the Rust runtime and interpreter return both files and directories and also
   follow directory symlinks through `Path::is_dir`.
 
 A symlink cycle can therefore recurse indefinitely, and callers can observe
 different entry sets across interpreter/native runtimes. The fast duplicate
 gate filters `.spl` paths, but a directory named `*.spl` can still be counted
 under the Rust behavior.
 
 ## Required solution
 
 Make every `rt_dir_walk` implementation return files/non-directory entries
 only, classify children without following symlinks, and add parity coverage for
 a regular file, nested directory, directory named `x.spl`, file symlink, and
 directory-symlink cycle. Keep sorting in callers that require deterministic
 report order.
 
 A pure-Simple wrapper cannot close this bug: `rt_dir_walk` completes traversal
 before returning, while the available Simple file-kind probes also follow
 symlinks. The fix must therefore land in the C, Rust SFFI, and interpreter
 runtime owners (`lstat`/`DirEntry.file_type()`/Windows reparse metadata), with
 the wrapper remaining only the shared caller facade.

## Resolution (2026-07-17)

The POSIX C owners now classify with `lstat`, Windows rejects reparse points as
directories, and both Rust owners use `DirEntry.file_type()`. The core-C archive
also exports the same non-following walker; its missing symbol was found by the
native focus reproducer. Rust SFFI, Rust interpreter, and core-C native cycle
tests pass with the exact four-entry fixture. The Simple source parity spec is
retained for the next admitted pure-Simple test-runner pass.

## Interpreter over-count (P2, 2026-07-18)

**Status: already fixed by this doc's own resolution commit — verified, no
new code fix needed.**

Lane S90 additionally reported (while landing the native fix above) that the
Rust-seed *interpreter*'s `rt_dir_walk` over-counted directory entries: for
`src/app/cli` (ground truth `find src/app/cli -type f | wc -l` = 76 files, 0
symlinks, 4 non-root subdirectories), the interpreter reportedly returned 80 —
exactly `files + subdirectories`.

### Root cause (pre-fix, now historical)

Before commit `a6822a52dee` ("fix(runtime): stop directory walks following
links", 2026-07-17), `rt_dir_walk`'s recursion in
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` was:

```rust
for entry in entries.flatten() {
    let path = entry.path();
    results.push(Value::text(path.to_string_lossy().to_string())); // pushed unconditionally
    if path.is_dir() {
        walk_recursive(&path, results); // AND recursed
    }
}
```

Every directory entry was pushed into the result **and** recursed into,
double-counting each directory once per level. For a symlink-free tree this
inflates the count by exactly the number of subdirectories — 76 files + 4
subdirs = 80, matching the report exactly.

### Why it's already resolved

`a6822a52dee` changed this to classify via `entry.file_type()` first: push
only when the entry is **not** a directory, recurse when it **is** — the same
diff that fixed the C/Rust-SFFI symlink-cycle parity bug documented above
also happened to fix this over-count as a side effect, because it replaced
the unconditional push with an `if/else`. Confirmed:

- `a6822a52dee` is an ancestor of this worktree's HEAD
  (`git merge-base --is-ancestor a6822a52dee HEAD`, exit 0) and no commit
  since has touched `file_io.rs` (`git diff a6822a52dee HEAD -- .../file_io.rs`
  is empty).
- Rebuilt the seed (`cargo build --release --bin simple`) and reran the
  ground-truth repro three ways, all returning **76** (matching `find -type f`
  exactly, no over-count):
  - `use std.io_runtime.{dir_walk}` (the extern-delegating facade)
  - `use app.io.{dir_walk}` (the app CLI facade)
  - a bare `extern fn rt_dir_walk(path: text) -> [text]` call, both with and
    without a trailing slash on the path
  - also reconfirmed against the shared pre-built `bin/simple` (fresh seed at
    `/home/ormastes/dev/seed_fresh_20260718/simple`)

### Regression coverage added

`file_io.rs`'s existing `dir_walk_emits_links_once_without_following_directory_cycles`
test already covered this class of bug indirectly (asserts non-symlink
directories `nested`/`x.spl` do NOT appear as entries), but had no symlink-free
fixture pinned to the literal `src/app/cli` shape. Added
`dir_walk_counts_files_only_not_directories_themselves`: 1 top-level file + 4
subdirectories each containing 1 file, asserts the walk returns exactly 5
entries (never 5 + 4 = 9). Both tests pass:
`cargo test --release -p simple-compiler --lib interpreter_extern::file_io::tests::dir_walk`
→ `2 passed; 0 failed`.

No other `dir_walk`-named facade in `src/lib`/`src/app/io` (there are several,
e.g. the pure-Simple shell-out `find -type f` wrapper in
`src/app/io/dir_ops.spl` and `src/lib/nogc_sync_mut/io/dir_ops.spl`, and the
unrelated mock stub in `src/lib/nogc_sync_mut/file_system/dir_ops.spl` which
always returns fixture data and is not reachable from real directory scans)
reproduces an over-count either; all tested facades agree with ground truth.
