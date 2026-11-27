# std.io_runtime ranged read export missing

Status: OPEN; source repair and four regression cases authored, UNEXECUTED.

Caret Phase4 HIR with Phase2 producer aa404 and a0 sources reported missing file_read_text_at_nullable in native_formats.spl. The physical io_runtime owner already defines and exports the checked operation, but the root facade shadows that module and omits it. The repaired facade exposes the same declaration via the SoSix host facade, under its existing name and a sosix alias, with no additional native wrapper or application host calls.

Tests: test/01_unit/lib/std_io_runtime_ranged_read_spec.spl; fixture test/fixtures/io_runtime/ranged_read_ascii.txt. These assert exact ranged bytes through both names, negative offset, missing positive-size read and existing-file zero-size read. Runtime code is unchanged: host_path_native and checked provider own Windows binary file reads, POSIX reads and platform errors; macOS/FreeBSD/SimpleOS execution remains unverified. No essential binary or runtime is qualified by this source repair.

**Revalidated 2026-11-02: still plausible because OPEN; source repair and four regression cases authored, UNEXECUTED; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-05 verification evidence (worktree work/libbug-w7-iort-20261105, aarch64 Linux, host phase1_1793422538 simple CLI, interpreter mode, cwd = worktree root)

Commands and results:

1. `simple test test/01_unit/lib/std_io_runtime_ranged_read_spec.spl --mode=interpreter --clean` → **OK, 4/4 passed** (both facade names exact-range, negative offset nil, missing-file positive-size nil, zero-size existing Some("")). The previously UNEXECUTED regression cases now have real behavioral results on a POSIX host.
2. `simple test test/01_unit/lib/std_io_runtime_facade_gap_spec.spl --mode=interpreter --clean` → **OK, 4/4 passed** — facade still exposes the pinned symbols; no export-drop regression from the ranged-read facade line.
3. `simple test test/01_unit/lib/gc_async_mut/slang/model_executor/native_formats_spec.spl --mode=interpreter --clean` → 11/14 passed. **All four tests exercising `file_read_text_at_nullable` pass** (GGUF magic, no-magic refusal, safetensors JSON header at byte 8, lowest-numbered shard entry) — the original missing-export consumer now resolves end-to-end through `std.io_runtime`. The 3 failures (`reads MemAvailable from the host`, `admits a model that comfortably fits`, `counts headroom against the budget`) are unrelated to this bug: pre-existing, environment-specific procfs gap — `read_file("/proc/meminfo")` returns "" because whole-file reads of size-0-stat files fail, while the checked ranged read of the same path succeeds (verified by probe: ranged read of /proc/meminfo returns the requested 100 bytes). Fix commit 5d677039694 touched only the facade export line + spec, so it cannot cause these.

Residual gaps (unchanged, not verifiable on this host): macOS/FreeBSD/SimpleOS lanes remain unverified; no essential binary/runtime qualification was performed by this verification.

Status note: bug_db.sdn intentionally NOT modified (verification-only mandate).
