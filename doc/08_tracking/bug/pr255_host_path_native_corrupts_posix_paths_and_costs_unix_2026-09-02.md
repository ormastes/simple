# PR #255 `host_path_native` corrupts POSIX filenames and taxes every Unix file op

Status: OPEN. Found 2026-09-02 by measurement on Windows 11 (seed `bin/simple.exe`,
16,347,136 bytes, 2026-09-01 17:54). Engine: `run` = Cranelift JIT.

## Where

`src/lib/nogc_sync_mut/fs/host_path.spl` (new in PR #255, OPEN, head `54ab7186f67`).
Wired into **every** operation in `src/lib/nogc_sync_mut/io/file_ops.spl`:
`rt_file_exists`, `rt_file_read_regular_no_follow_bounded`, `rt_file_write_text_at`,
`rt_file_write_bytes`, `rt_file_atomic_write`, `rt_file_size`, `rt_file_stat`,
`rt_file_hash_sha256` — each calls `host_path_native(path)` first.

## Defect 1 — POSIX path corruption (correctness, severe)

`host_path_native_for` runs `host_path_canonical(path)` = `path.replace("\\", "/")`
**unconditionally, before** the platform check. A backslash is a LEGAL character in
a POSIX filename, so on Linux/macOS the conversion rewrites real filenames.

Measured, byte-for-byte:

| input | output |
|---|---|
| `/home/a\b.txt` (13 bytes) | `/home/a/b.txt` (13 bytes) |

**The length is identical**, so a length-only assertion cannot see this. The result
is that a Linux file op on any path containing `\` silently addresses a different
file. This is the exact hazard for which the dead `unix_to_windows` trio was
deleted on 2026-09-01; `to_native_path` in `platform.spl` deliberately uses
IDENTITY as its non-Windows branch for this reason.

## Defect 2 — Unix overhead (violates the stated NFR "no overhead on linux")

The `.replace()` scan+alloc happens before the guard, and the guard itself
(`_host_is_windows`) calls `.lower()` (an allocation) plus four `.contains()` scans.
Min-of-3 wall, 5,000,000 iterations each, same box, same seed:

| variant | min wall | note |
|---|---|---|
| PR #255 shape (`.replace()` then `.lower()` + 4x `.contains()`) | **11,688 ms** | current code |
| replace-first, cheap literal guard | 6,516 ms | |
| guard-first, cheap literal guard | 2,511 ms | |
| bare function call, no conversion | 907 ms | |
| **cached bool guard, identity early-return** | **421 ms** | the floor |

**~28x** the floor, roughly **2.25 us per call**, paid on every file operation on
Linux. Caveat, stated rather than hidden: the cached-bool variant measures below
the bare-call variant, which indicates the JIT eliminates part of it — that is the
desired outcome, but it means 421 ms is a floor, not a precise per-call cost.

## Defect 3 — drive-letter case conflicts with the specified conversion

Specified: `/d/foo/bar` -> `d:\foo\bar`. Measured output: `D:\foo\bar` (`.upper()`
in `_mingw_drive_to_windows`). Windows treats these equivalently; test fixtures and
log comparisons do not. Needs an explicit decision, then consistency.

## Defect 4 — relative path with a single-letter first segment becomes a drive root

`_mingw_drive_to_windows` admits a compact `c/rest` spelling. Measured:
`c/foo` -> `C:\foo`. A relative directory literally named `c` is rewritten to the
root of drive C:. Combined with `rt_file_atomic_write` this is a data-loss shape.

## Fix sketch (not applied)

1. Make the platform decision the FIRST statement and return `path` unchanged on
   the non-Windows branch — no `.replace()`, no `.lower()`, no scan, no alloc.
2. Hoist the platform decision to a computed-once value; do not call
   `rt_platform_name()` + `.lower()` per path.
3. Move `host_path_canonical` (`\` -> `/`) INSIDE the Windows branch. It is only
   ever correct there.
4. Drop the bare `c/rest` rule, or require an absolute context for it.
5. Decide drive-letter case and pin it with a byte-length + byte-content spec.

## Related

- `doc/08_tracking/bug/lexer_drops_backslash_escape_in_string_literal_2026-09-02.md`
- `src/lib/nogc_sync_mut/platform.spl` `to_native_path` (identity on non-Windows)
- `src/lib/common/path_pure.spl` `to_slash` / `to_backslash`

## Defect 5 — no spec covers `host_path_*` itself

PR #255 adds two specs (`system_location_spec.spl`, `lazy_path_literal_spec.spl`);
neither exercises `host_path_canonical` / `host_path_native_for` /
`host_path_native`. The function is now on the path of every file operation AND
every process spawn (`_io_runtime_process_spawn_async_raw`,
`_io_runtime_process_run_timeout_raw`, `rt_file_rename`, `rt_file_move`,
`rt_dir_remove_all`) with zero direct coverage.

## Census — `c:\`-style literals in `src/**/*.spl`

Method note: the `grep` on PATH and the shell both collapse backslash needles
(a `'C:\'` single-quoted assignment measured `${#N}` = 3, not 4), which produced
two wrong counts before this one. The trustworthy method is `git grep -P` with
**hex escapes**, so no backslash appears in the pattern at all:

```
git grep -nIP '[A-Za-z]:\x5C\x5C' -- 'src/**/*.spl'
```

Result: **38 lines across 21 files**. Most are `:\n` escaped-newline artifacts in
generated-code string builders, not paths. The genuine drive-letter path literals
are **7 lines in 5 files**:

| file:line | literal | lexes to |
|---|---|---|
| `src/app/test_runner_new/test_runner_async.spl:46` | `"C:\Temp"` | **`C:Temp`** (corrupt) |
| `src/compiler/70.backend/linker/link_deps.spl:159` | `"C:\Windows\System32\{lib}.dll"` | **corrupt** |
| `src/compiler/70.backend/linker/link_deps.spl:160` | `"C:\Windows\SysWOW64\{lib}.dll"` | **corrupt** |
| `src/compiler/70.backend/linker/msvc.spl:236` | `"C:\Program Files (x86)\...\vswhere.exe"` | **corrupt** |
| `src/compiler/70.backend/linker/msvc.spl:323` | `"C:\Program Files (x86)\Windows Kits\10\Lib"` | **corrupt** |
| `src/app/llm_caret/.../PowerShellTool/pathValidation.spl:4` | `"...C:\\"` | `C:\` (OK, trailing) |
| `src/app/wine_process_session_plan/main.spl:37` | `"C:\\"` | `C:\` (OK, trailing) |

The five marked corrupt are **broken today, independent of PR #255** — a trailing
`\` lexes correctly, an embedded one does not (measured: `"C:\Temp"` -> 6 bytes
`C:Temp`; `"C:\Windows\System32"` -> 17 bytes `C:WindowsSystem32`). Under the
user's rule ("no `c:\` style path in code; only mingw/linux style") all seven are
violations regardless.

---

## RESOLUTION 2026-09-02 — all five fixed on the current tree, not on the PR branch

Landing model: PR #255 is BEHIND main and its converter is defective, so the
FIXED converter was authored on the current tree at the PR's exact path
(`src/lib/nogc_sync_mut/fs/host_path.spl`). When the PR rebases, main's version
wins that conflict. The PR's own wiring (file_ops, process_ops, io_runtime, the
lexer work, `system_location.spl`) was deliberately NOT recreated here — it is
correct and belongs to the PR.

Commits, one per defect, on top of `a95e877484a` (detached HEAD, not pushed);
the tip is also at `refs/wip/pr255-host-path-fixes`:

| sha | defect |
|---|---|
| `3f3a52ca37e` | baseline: PR #255 converter imported verbatim, so each fix is an isolated diff |
| `74ce8a6269c` | D1 — platform guard first; POSIX identity |
| `d3f9c1c348c` | D2 — cached bool, first-statement identity return |
| `bbb9f897277` | D3 — lower-case MinGW drive letter; preserve an existing one |
| `dc101ee1fd3` | D4 — compact `c/rest` rule removed |
| `2e8eb2dfa6d` | collision — `to_native_path` folded into `host_path` |
| `47796bfef23` | D5 — converter spec + corrected D2 figures |

### D1 — fixed, with a byte-level proof and a negative control

`host_path_native_for` now opens with `if not _host_is_windows(platform): return path`;
the `\` -> `/` canonicalisation moved inside the Windows branch.
`host_path_canonical` gained a `host_path_canonical_for` seam with the same
identity contract. Measured through the injected `"linux"` / `"macos"` /
`"freebsd"` seam:

| input | before | after |
|---|---|---|
| `/home/a\b.txt` (13 B) | `/home/a/b.txt` (13 B) | `/home/a\b.txt` (13 B) |

NEGATIVE CONTROL (executed, not asserted): re-introducing the pre-fix ordering
turns the new spec RED with `assert_equal failed: expected /home/a\b.txt, got
/home/a/b.txt`. The spec is not vacuous.

### D2 — re-measured on this box

Cached process-lifetime bool (`host_is_windows_host`, backed by a one-cell
module `var`), then a first-statement identity return. `_host_is_windows` also
grew an exact-match fast arm for the three names the runtime emits, so even the
uncached seam avoids the `.lower()` allocation. Min-of-3, 5,000,000 iterations,
JIT lane, both variants forced onto the non-Windows branch:

| variant | min wall |
|---|---|
| PR #255 shape (`.replace()` then `.lower()` + 4x `.contains()`) | **9,473 ms** |
| bare call, no conversion | 36 ms |
| **cached bool + first-statement identity return** | **76 ms** |

~125x off the pre-fix shape; ~1.9 us/call down to ~15 ns/call. The absolute
numbers differ from the original harness above (36 ms for a bare call indicates
the JIT elides part of the loop) — the RATIO is the claim, not the microsecond.

### D3 — DECISION: lower-case for the MinGW form, case-PRESERVING otherwise

`/d/foo/bar` -> `d:\foo\bar`, matching the specified conversion. Input that
already carries a drive letter falls through untouched, so `C:/tmp/probe.txt` ->
`C:\tmp\probe.txt`. That case-preserving idempotence is a PREREQUISITE for the
fold: `test/01_unit/lib/common/path_native_separator_boundary_spec.spl:60`
asserts exactly that pair, and a lower-casing converter would break it. The
redundant third branch that re-`upper()`ed an existing drive letter is deleted.

### D4 — DECISION: removed from the universal boundary, not conditioned

`c/foo` -> `c\foo` (separator conversion only), was `C:\foo`. The rule belongs in
`{sys:...}` desugaring, where the input is known to be a system-location
template and a single-letter first segment cannot be an ordinary relative
directory. That desugaring exists only in PR #255, so this tree removes the rule
and the PR author relocates it.

### D5 — `test/01_unit/lib/nogc_sync_mut/fs/host_path_spec.spl`, 7/7 green

Every assertion checks bytes AND `.len()`. Backslashes are built from a
standalone `"\\"` literal — the lexer silently drops an embedded backslash
escape, so the obvious spelling cannot be used (see the related record).

### Collision — RESOLVED in favour of `host_path`

`platform.to_native_path` (zero product callers, duplicated across
`platform.spl:127` and the SHADOWING `platform/__init__.spl:111`) is now a thin
alias for `host_path_native` in BOTH copies. Rationale in order: host_path is
the mechanism that is actually wired; it is a strict SUPERSET (it also handles
`/d/foo`, which `to_native_path` never did, so no existing caller changes
behaviour); and it is cheaper — `is_windows()` -> `host_os()` SPAWNS
`/bin/sh -c "uname -s"` on every non-Windows call, which the fold silently
removes from that path. The names are kept, not deleted: they are the documented
public spelling and they have specs. Both existing path specs stay green
(3/3 and 6/6).

### Not fixed here

- The five genuinely corrupt `c:\` literals (`link_deps.spl:159-160`,
  `msvc.spl:236,323`, `test_runner_async.spl:46`) are untouched — `70.backend`
  and `scripts/` are owned by other live sessions this session was told to avoid.
- No POSIX execution was possible on this host (Windows 11). Every Unix claim
  above is asserted through the explicit-platform seam, and says so.

### Addendum — the fix chain is NOT contiguous; one foreign commit is interleaved

The table above says "one per defect, on top of `a95e877484a`", which implies a
contiguous chain. It is not one. Another session committed on the same shared
detached HEAD mid-sequence, so `77fa84919c4`
("fix(check): strict pattern — 6,617 hits were mostly escape sequences") sits
between D4 (`dc101ee1fd3`) and the fold (`2e8eb2dfa6d`), and every later commit
here is parented on it.

That commit is not inert with respect to this work: it touches
`scripts/check/check-no-windows-style-paths.shs` (+7/-1) **and DELETES
`src/lib/nogc_sync_mut/fs/host_path.spl` outright (-111 lines)** — i.e. it
removed the converter this record is about. The file was restored by the D5
commit `47796bfef23` and is intact at the tip (113 lines; guard-first at :41 and
:75, lower-case drive at :65, cached bool at :86). Verified with
`git cat-file -p HEAD:src/lib/nogc_sync_mut/fs/host_path.spl`.

**Landing instruction.** Cherry-pick exactly these eight, in order, and EXCLUDE
`77fa84919c4` (it is another session's work and would re-delete the converter if
replayed out of order):

```
3f3a52ca37e  74ce8a6269c  d3f9c1c348c  bbb9f897277
dc101ee1fd3  2e8eb2dfa6d  47796bfef23  5e9a0abd2e3
```

The whole tip is also reachable at `refs/wip/pr255-host-path-fixes`, but that ref
carries `77fa84919c4` too — do not land the ref wholesale without deciding about
that commit separately with its author.
