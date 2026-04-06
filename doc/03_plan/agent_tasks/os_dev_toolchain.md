# Agent Tasks: SimpleOS Dev Toolchain

## Task Assignment

### Agent: code-1 — VCS App Complete Implementation
**Priority:** P0 (blocking)
**Files:**
- `src/os/apps/vcs/vcs_app.spl` — Complete VCS with VFS file I/O
- `src/os/apps/vcs/mod.spl` — Module exports

**Deliverables:**
1. `VcsEngine` class with VFS-backed storage operations
2. `vcs_run(cwd, args)` — CLI dispatcher (init/add/commit/log/status/diff/checkout)
3. File-level snapshots using directory copies under `.vcs/objects/<hash>/`
4. Commit chain via parent links in `.vcs/commits/<hash>.txt`
5. Staging area in `.vcs/staging/`

### Agent: code-2 — Shell VCS Integration
**Priority:** P1
**Depends:** code-1
**Files:**
- `src/os/apps/shell/shell_app.spl` — Add `vcs` builtin (no edit — separate tool)

**Deliverables:**
1. Document how shell calls VCS: `vcs init`, `vcs add file`, etc.
2. VCS is a standalone tool invoked via process spawn, not a shell builtin

### Agent: test-1 — VCS System Test
**Priority:** P1
**Depends:** code-1
**Files:**
- `test/system/os/vcs_system_test.spl` — Full VCS workflow test

**Deliverables:**
1. init → add → commit → log → modify → diff → commit → log (2 commits)
2. checkout old commit, verify file restored
3. status shows modified/staged/untracked
4. Deterministic hash verification

### Agent: test-2 — Full Capabilities Test
**Priority:** P1
**Files:**
- `test/system/os/simpleos_capabilities_test.spl` — Already done (63 tests)

**Status:** COMPLETE ✅

### Agent: docs-1 — Porting Roadmap
**Priority:** P2
**Files:**
- `doc/05_design/os_dev_toolchain_porting.md` — Already done

**Status:** COMPLETE ✅

## Execution Order

```
Phase 1: code-1 (VCS implementation)     ← NOW
Phase 2: test-1 (VCS system test)        ← parallel with code-1 finish
Phase 3: Run all system tests            ← validation
Phase 4: VCS sync (commit)               ← final
```
