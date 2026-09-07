# `rt_mmap`'s path argument is the one unwrapped path site in `file_ops.spl`, falsifying PR #255's "every operation" claim

**Date:** 2026-09-06 · **Status:** RECORDED (measured, not fixed) · **Measured at:** `a12a19eb775`
(worktree checkout of `origin/main`); reported at `4699194f81e`. No build was run.

## The site

```
src/lib/nogc_sync_mut/io/file_ops.spl:25:extern fn rt_mmap(path: text, size: i64, offset: i64, readonly: i64) -> i64
src/lib/nogc_sync_mut/io/file_ops.spl:274:        rt_mmap(path, size, offset, if readonly: 1 else: 0)
```

`path` reaches the raw extern exactly as the caller supplied it. Every other path-taking
`rt_*` call in the same file routes its argument through `host_path_native` from
`src/lib/nogc_sync_mut/fs/host_path.spl` (defined at `:99`, with
`host_path_native_for(path, platform)` at `:68`). `grep -c host_path_native
src/lib/nogc_sync_mut/io/file_ops.spl` = **19**, of which one is the import, so **18 call
sites** — matching the count reported to this session — plus this one site that is not.

`rt_mmap` is not simply forgotten: the surrounding block was deliberately edited. Lines
264-273 add a guard with a written rationale:

```
    # return the documented invalid-handle sentinel -1 without entering the
    # raw `rt_mmap` boundary. `rt_mmap` is not registered in every execution
    # lane (the interpreter lane aborts with `unknown extern function:
    # rt_mmap`), so without this guard the negative-handle contract this
    # function promises is unobservable there. Existence is probed through the
    # typed `file_exists` alias above rather than a new raw `rt_*` call site.
    if path == "" or size <= 0 or offset < 0 or not file_exists(path):
        return -1
```

So the author of that guard was in this exact function, reasoning about this exact `path`
value, and routed the *existence probe* through the typed `file_exists` alias while leaving
the `rt_mmap` argument itself raw. `file_exists` does wrap. The result is that one path
value is normalised for the existence check and not normalised for the mapping call — the
two can disagree.

## Why this is filed as an inconsistency, not as "wrap it"

The obvious fix is not obviously correct, and this record deliberately does not recommend
one. `doc/08_tracking/bug/pr255_host_path_native_corrupts_posix_paths_and_costs_unix_2026-09-02.md`
is **OPEN** and reports that `host_path_native` *corrupts* POSIX filenames:
`host_path_native_for` runs `path.replace("\\", "/")` unconditionally before the platform
check, and a backslash is a legal POSIX filename character, so `/home/a\b.txt` becomes
`/home/a/b.txt` on Linux and macOS. On that reading, `rt_mmap` is the only site in the file
that is *correct*, and the 18 wrapped sites are the defect.

What is unambiguous either way is that `file_ops.spl` currently applies two different path
conventions to the same kind of value in one file, without a comment anywhere saying which
is intended — and that whichever convention wins, one set of sites is wrong.

## A factual correction to the PR #255 record

That record states, at line 9:

> Wired into **every** operation in `src/lib/nogc_sync_mut/io/file_ops.spl`

That is false at this sha. `rt_mmap` is an operation in that file and is not wired. The
enumeration that follows in the PR #255 record (`rt_file_exists`,
`rt_file_read_regular_no_follow_bounded`, `rt_file_write_text_at`, `rt_file_write_bytes`,
`rt_file_atomic_write`, `rt_file_size`, `rt_file_stat`, `rt_file_hash_sha256`) is a list of
`rt_file_*` symbols; `rt_mmap` does not carry that prefix and fell outside the sweep. The
word "every" should be narrowed to "every `rt_file_*` operation", so that the remaining gap
is visible rather than asserted away.

## Distinct from the existing `rt_mmap` record

`doc/08_tracking/bug/rust_runtime_rt_mmap_stub_blocks_host_gpu_2026-07-12.md` concerns the
Rust runtime's `rt_mmap` being a *stub* — a provider-side implementation gap. This record
concerns the *caller-side* path convention at one `.spl` call site. Different file,
different lane, different defect; neither subsumes the other. `grep -rl host_path_native
doc/08_tracking/bug/` returns only the PR #255 record, so the call-site gap is unfiled.

## What was NOT established

- **No runtime evidence.** No mapping was performed with a backslash-bearing path, on any
  platform, in any lane. The divergence between the wrapped `file_exists` probe and the
  unwrapped `rt_mmap` argument is established by reading the source, not by observing a
  failure. Whether it is reachable in practice depends on whether any caller passes a path
  containing a backslash, which was not surveyed.
- **Not surveyed beyond this file.** Other modules the PR #255 record names as wired
  (`process_ops`, `io_runtime`) were not audited for the same class of miss. There may be
  more.
- **No fix, and no recommendation of one.** Wrapping the site would propagate the open
  PR #255 corruption defect to one more call path; unwrapping the other 18 is a larger
  change than this record's evidence supports. The decision belongs to whoever resolves
  PR #255.
