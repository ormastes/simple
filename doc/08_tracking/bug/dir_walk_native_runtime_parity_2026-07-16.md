# Native directory walk runtime parity

Status: Open.

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
