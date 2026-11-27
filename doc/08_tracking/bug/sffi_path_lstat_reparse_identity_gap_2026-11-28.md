# SFFI gap: no public lstat / reparse-point / readlink / identity / bounded-process surface (blocks the `.spl` port of `unchanged-materialized-alias.py`)

Date: 2026-11-28. Status: OPEN (port BLOCKED). Owner decision (2026-11-27): port
`scripts/audit/unchanged-materialized-alias.py` to `.spl` using the std fs /
Windows reparse API; if the API is missing, file an SFFI gap and mark BLOCKED.
This is that record. The `.py` stays as is until the API below exists.

## Sole caller

`scripts/audit/direct-env-runtime-guard.shs:203` (only in `--working` mode with a
`.git` present):

```sh
if [ -n "$alias_python" ] && "$alias_python" scripts/audit/unchanged-materialized-alias.py "$path"; then
    continue
fi
```

The guard already falls back to scanning the file (and reporting findings) when
the classifier is unavailable: with no `python3`/`python` on PATH `alias_python`
is empty and the `if` is skipped, so the file is scanned normally. So the gap
costs only a missed false-positive suppression for exact-HEAD duplicates
("materialized aliases"), never a missed finding. Any `.spl`/`.shs` replacement
must keep that contract: classifier unavailable or ambiguous => keep scanning.

## What the Python needs, and what std offers today

Verified 2026-11-28 by grepping `src/lib/**` and `src/app/io/**` at
`origin/release/1.0.0`.

| Python function (line) | Needs | Public surface today |
|---|---|---|
| `reparse(path)` (124) | lstat of the LEAF without following: `S_ISLNK(st_mode)` on POSIX, `FILE_ATTRIBUTE_REPARSE_POINT` (0x400) on Windows | none. `file_is_symlink` (`nogc_sync_mut/file_system/metadata.spl:79`) is a heuristic ("exists, not a regular file and not a real dir"): it also returns true for sockets/FIFOs, returns false for a DANGLING link, and on Windows cannot tell a junction/OneDrive placeholder from a symlink. `rt_dir_is_real_no_follow` is directory-only |
| `identity(path)` (139) | tuple `(st_dev, st_ino, st_mode, st_size, st_mtime_ns, st_ctime_ns)` of the leaf, no follow | none (`file_mode_bits`, size, mtime exist separately and follow links; no dev/ino/ctime_ns; they are separate syscalls so the tuple is not atomic) |
| `unchanged()` readlink compare (176) | link target TEXT (`os.readlink`) | none. `symlink_read` (`nogc_sync_mut/file_system/utilities.spl:203`) is a documented stub that always returns nil ("runtime exposes no readlink(2) primitive"). `path_identity_abi.spl` declares a private one-byte `readlink` probe only |
| `unchanged()` samefile (203, 211) | "same file" = equal `(st_dev, st_ino)` (Windows: volume serial + file index via `GetFileInformationByHandle`) | none. `path_identity_same/contains` (`nogc_sync_mut/io/path_identity.spl:14,17`) compare resolved FINAL PATH text, which is not inode identity (hard links, case-insensitive volumes, 8.3 names differ) |
| `plain_chain` (130) | per-component no-follow reparse check from repo root to leaf | composable from the lstat surface above; not available today |
| `Budget.git` (45-71), `cancel` (35) | spawn `git` with stdin devnull, stdout capped by `MAX_METADATA_BYTES`, stderr discarded, a hard wall-clock deadline and kill+reap of the child | `process_ops`/`process_observation_v1` observe start/poll/result but there is no documented bounded run (deadline + output byte cap + guaranteed kill/reap) that is usable from a short-lived script |
| `bounded_file` (95) | open, `fstat` the SAME handle, size bound before read (TOCTOU-safe) | `file_ops` has root-confined open that refuses reparse points (`file_ops.spl:177`); no size-bounded read of an already-open handle |

`path_entry_present` and `path_final_existing` (`path_identity.spl`) cover only
"does an entry exist" and "resolved final path text".

## Proposed minimal API (new owner `std.nogc_sync_mut.io.path_lstat_v1`)

Names follow the existing `*_v1` / `Result<T, text>` convention; each function
is a thin, unsafe-bounded ABI wrapper with an explicit failure status (no nil
conflation, per the `rt_dir_*` notes in `dir_ops.spl`).

```text
enum PathKindV1: Regular | Directory | Symlink | ReparseOther | Other

struct PathLstatV1:
    kind: PathKindV1
    reparse: bool        # POSIX: kind == Symlink; Windows: attr & 0x400
    dev: u64             # st_dev | VolumeSerialNumber
    ino: u64             # st_ino | FileIndex (high<<32|low)
    mode: u32            # st_mode | synthesized from attributes
    size: u64
    mtime_ns: i64
    ctime_ns: i64        # POSIX ctime | Windows ChangeTime

fn path_lstat_v1(path: text) -> Result<PathLstatV1, text>      # NEVER follows the leaf
fn path_readlink_text_v1(path: text) -> Result<text, text>     # target bytes as text; Err if not a link
fn path_same_file_v1(a: text, b: text) -> Result<bool, text>   # (dev, ino) equality, follows both
```

- POSIX backend: `lstat(2)` / `readlink(2)` / `stat(2)`.
- Windows backend: open with `FILE_FLAG_OPEN_REPARSE_POINT | FILE_FLAG_BACKUP_SEMANTICS`,
  `GetFileInformationByHandle` for dev/ino/size/times and
  `FILE_ATTRIBUTE_REPARSE_POINT`; `FSCTL_GET_REPARSE_POINT` for the readlink
  text. `path_identity_abi.spl` already declares `GetFileAttributesW`/`readlink`
  privately; those declarations should move behind the new owner.
- Bounded child process (separate owner, also needed by other gates):
  `process_run_bounded_v1(argv, cwd, env, stdin_null, max_stdout_bytes, deadline_ms) -> Result<BoundedRun, text>`
  with guaranteed kill and reap of the child (and its group/job object) on
  deadline or cap breach, stderr discarded. A `.shs` port could instead use
  `timeout(1)` plus a `head -c` byte cap if the `.spl` requirement is relaxed.
- Dual-run twin per `doc/07_guide/os/hal/pure_simple_hal.md`: the C boundary
  (if any) gets a Simple twin; no `libsqlite`-style external dependency is
  involved.

## Census / bookkeeping

`doc/08_tracking/todo/python_phase_census_2026-11-27.md` row for
`scripts/audit/unchanged-materialized-alias.py` is BLOCKED and links here.
Re-evaluate when `path_lstat_v1` + a bounded process primitive land; until then
the Python stays (Python is allowed before phase 2; the caller degrades to
scanning when it is missing).

## Acceptance for closing this gap

1. `path_lstat_v1`, `path_readlink_text_v1`, `path_same_file_v1` public with unit
   specs covering: regular file, directory, symlink, dangling symlink, hard link
   (same inode), Windows junction and file symlink, case-folded alias.
2. A bounded process run with a hung-child spec (deadline kill + reap, output cap).
3. `unchanged-materialized-alias` ported to `.spl` with a differential spec
   against the Python on the same fixtures, then the `.py` removed.
