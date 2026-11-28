# Python port blockers: cgroupfs helper SFFI gaps, wrapper startup cost (2026-11-27)

Lane: p3+ perf/dev-tool Python ports (census `python_phase_census_2026-11-27.md`).

## TODO-A: stage3 cgroupfs helper needs missing SFFI surfaces (BLOCKED)

Files: `scripts/bootstrap/lib/stage3-cgroupfs.py`, `test/00_quick/bootstrap/stage3_cgroupfs_kernel.py`.
The helper is bootstrap authority (hash-pinned to HEAD by `scripts/bootstrap/resume-stage3-from-admitted.sh`),
so a port must change that pin together with the caller and the root-only kernel regression.

Searched `src/lib` (2026-11-27). Present: Linux `open`, `openat(dir_fd, path, flags, mode)` (so `O_NOFOLLOW`
and `O_DIRECTORY` walks), `read`, `pread`, `write`, `close`, `fsync`, `statx`, `geteuid`
(`src/lib/nogc_sync_mut/io/retained_file_abi.spl`). Missing, each needed by the helper:

1. `setuid` / `setgid` / `setgroups` / `initgroups` and `getpwnam` (uid/gid/home lookup) for the privilege drop.
2. A pre-exec hook or privilege-drop spawn: the child must write its pid into the supervisor `cgroup.procs`
   and drop uid between fork and exec; `process_run*` only offers argv/env spawn.
3. `os.chown`/`os.chmod` by path (no fchown/fchmod needed), `Path.mkdir`/`rmdir` equivalents (the helper uses path-based mkdir/rmdir, not mkdirat/unlinkat), and `fstatat(dir_fd, AT_SYMLINK_NOFOLLOW)` for the root-controlled checks (`statx` exists; confirm it covers dir-fd-relative lstat).
4. Signal handlers that raise inside provisioning (SIGTERM/SIGINT/SIGHUP) and `SIG_IGN` during cleanup.
5. Own session / pid-wait with raw wait status (`start_new_session`, `child.wait`).

Verify path once unblocked: WSL `ubuntu-p2` under `/dev/shm`, single `wsl` invocation, real cgroup v2 delegation.
Census rows for both files are marked BLOCKED with this todo.

## TODO-B: `simple run` startup per wrapper invocation (PERF)

Measured 2026-11-27 (seed, loaded Windows host, 10 runs): Python wrapper 1.65 s/run, the `.spl` twin
(`scripts/tool/riscv64-unknown-elf-tool-wrapper.spl`) 4.49 s/run, i.e. about 2.8 s of extra startup per
invocation. This matters for per-compile wrappers (one wrapper process per translation unit).
Fix: build the wrapper natively once a pure-Simple binary is deployed (`.cmd` shims then call the native exe),
and re-measure; until then keep the interpreter path.
