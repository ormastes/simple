# workaround_store_git_ls_files_timeout_scv_admission_2026_11_09

P1. `src/app/bug/workaround_store.spl` ran `git ls-files --cached --others --exclude-standard -z` over the whole tree with a hard 30 s timeout and 16 MiB output bound. A case root with 123,624 untracked files under `build/scv` (no root .gitignore) took 11-45 s and ~16.3 MB, so native builds died with `workaround Git failed (-1): TIMEOUT 30000ms` -> `SCV-E-ADMISSION: git-event-refresh-failed`, blocking phase 3 stage2 case runs.

Fix: discovery (full scan and status) is scoped by pathspec to source suffixes and excludes build/, .simple/, .worktrees/ and vendor trees; timeout (default 120 s) and output bound (default 64 MiB) are overridable via SIMPLE_WORKAROUND_GIT_TIMEOUT_MS / SIMPLE_WORKAROUND_GIT_MAX_BYTES and the error names them.

Repro/prevention: test/01_unit/app/bug/workaround_git_scope_spec.spl (real git fixture with 300 cache files + vendor file).
Not done: SCV writing its cache inside the scanned root without an ignore entry (the store no longer cares).
