# Hook path resolution prepends the worktree to backslash UNC paths

Date: 2026-09-30
Scope: main at 0814a6dfa5eef7c5acfdb629f5e7cf82ef817dd0.
Status: focused resolver regression PASS; standard push guards pending.

Independent review of the release Windows-drive fix found that main's
`is_absolute_path` recognizes POSIX and drive-qualified paths but misses
backslash-form UNC paths. The new literal oracle `\\server\share\hooks`
failed against that classifier: actual `D:/linked-worktree/\\server\share\hooks`,
exit 1. With the UNC absolute-path pattern, all nine resolver cases pass,
exit 0 (`PASS hook-path selftest: 9 cases`). This is the first focused cycle.

The fix adds the missing UNC pattern and routes hook-directory and cache
path resolution through `resolve_hook_path`. Both configured hook lookup and
its cache fingerprint now use the same path rule; previously those two sites
recognized only leading `/`, even though Git common-directory classification
already recognized drive-qualified paths. The existing relative common-directory
canonicalization against the current working directory remains in place.

`sh scripts/check/check-hook-installation.shs --selftest-paths` invokes the
production resolver. Nine literal expected paths cover drive-forward,
drive-backslash, lowercase drive, POSIX, both UNC slash spellings, relative Git
and hook paths, and a drive-relative path that must remain relative.

No hook configuration or shared hook file changes. The existing full guard
checks and normal push workflow remain active; a path selftest is not evidence
that the entire hook installation passes. This change is independent of the
runtime tagged-concat fix and its Linux-only C regression.
