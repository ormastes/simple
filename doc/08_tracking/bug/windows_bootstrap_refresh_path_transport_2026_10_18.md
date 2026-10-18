# Windows Stage 2 cache refresh rejects an MSYS-converted predecessor path

Status: source correction reviewed; focused Windows Bash controls passed.

## Observed failure

The sixth Windows bootstrap continuation used frozen source `bf2` and retained the fifth campaign's 1,361 completed native objects. It exited 64 after `phase1-snapshot-preserve`, before native compilation and without a source-transition record. The intended POSIX predecessor and transition-log paths independently passed the canonical-path validator.

The actual nested `bash.exe` invocation converted the refresh option to `--refresh-stage2-source-cache=D:/dev/.../predecessor`. The option parser retained that spelling; `bootstrap_cache_new_path_validate` accepts only POSIX absolute paths and rejected it silently. A read-only argv probe established the conversion. The diagnostic launcher correction scopes `MSYS2_ARG_CONV_EXCL` to `--refresh-stage2-source-cache=`; it changes argument transport without waiving any cache contract.

## Production correction

The existing `absolute_path` helper converts native drive-absolute paths with `cygpath -u`. After the helper is defined, only native drive-absolute refresh inputs are normalized through it. POSIX inputs remain unchanged; relative, drive-relative and UNC inputs are not promoted into accepted refresh authority. Native lexical dot, double-separator and trailing-separator forms are refused before conversion can collapse them. The existing physical-path and symlink validator remains in force and now reports a predecessor-path diagnostic on failure.

Producer identity, dependency-key owner, source transition snapshots, runtime/tool equality, writer ownership and object validation remain unchanged. No global MSYS argument-conversion setting is changed.

## Focused controls

`test/01_unit/scripts/bootstrap_cache_refresh_path_test.shs` extracts the actual production helpers and exercises canonical POSIX input, real Windows drive/backslash spellings (on Windows), paths containing spaces, relative and malformed paths, and a real symlink plus a child through that link. Native-strict symlink creation must succeed; a copied link substitute cannot pass. Non-Windows execution explicitly leaves native-drive coverage unmeasured.

The focused path test passed on Windows on 2026-10-18, including actual drive/backslash conversion and native-strict real symlink refusal. The existing `bootstrap_cache_source_refresh_test.shs` also passed its actual context, immutable transition, retained-object and incompatible-input/writer-refusal controls. Logs and private fixtures are retained under `build/windows-refresh-path-review` in the repair worktree. Shell syntax and whitespace checks passed.

These tests invoke no compiler and touch no production caches. Compiler qualification and an actual native-cache hit count remain separate pending evidence; the frozen compiler continuation uses the scoped launcher correction rather than this unmerged source change.
