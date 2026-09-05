# Stage 3 untracked fingerprint process storm

Date: 2026-08-11  
Status: FIX IMPLEMENTED; full bootstrap admission rerun pending

## Symptom

An immutable bootstrap snapshot eliminated concurrent-source publication races
and successfully published a fresh Rust authority. Stage 3 provenance then
spent more than ten minutes in `bootstrap_stage3_git_state` without reaching
the stage 2 build. The snapshot contained about 113,109 untracked paths and
2.4 GiB under `.claude`.

The run was stopped with exit 130 under the mandatory runaway guard. No stage 2
or stage 3 compiler was admitted.

## Root cause

`scripts/check/lib/bootstrap-stage3/authority.shs` iterates every untracked path
in POSIX shell and invokes `bootstrap_stage3_hash_file` separately for each
regular file. This is O(files) process creation in addition to O(bytes) hashing.
Large cooperative worktrees therefore turn an integrity gate into a process
storm before compilation starts.

A second correctness defect was fixed during diagnosis: default Git C-quoting
made non-ASCII untracked paths appear nonexistent. The function now requests
literal UTF-8 paths, and
`test/01_unit/scripts/bootstrap_stage3_unicode_git_state_test.shs` proves both
admission and content-sensitive fingerprinting.

## Required repair

Replace the per-file shell hash calls with one NUL-delimited, streaming manifest
owner. It must bind relative path bytes, kind, executable bit or symlink target,
and content digest in deterministic byte order. Nested repositories must retain
their existing explicit binding. Add scale evidence with at least 100,000
untracked files and a bounded warm/cold runtime target before retrying the full
bootstrap.

Excluding `.claude` or other cooperative state is not sufficient as the sole
fix: provenance must either bind excluded-root identity through an explicit
policy receipt or hash it efficiently.

## Implemented result

`bootstrap-stage3-untracked-manifest.pl` now owns the untracked manifest in one
process. It consumes NUL-delimited Git paths, sorts raw path bytes, and retains
file content, executable bit, symlink target, directory content, and nested
repository HEAD binding.

On the real immutable snapshot (113,109 untracked paths, including 2.4 GiB
under `.claude`) the optimized authority function completed in **36.11 s** with
**129,604 KiB** max RSS. The prior shell loop ran for more than ten minutes
without completing, so the measured lower-bound speedup is greater than
**16.6x**. This is provenance-only evidence; it is not a server benchmark.
