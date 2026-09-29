# std.path contract diverges from path_utils_spec (Windows handling, trailing-slash basename, case-insensitive ext)

Date: 2026-09-16
Spec: test/01_unit/app/tooling/path_utils_spec.spl (4 of 28 examples fail)

## Observed
Failing examples in `bin/simple test`:
- "extracts filename from unix path": `expected user to equal ` — `get_filename("/home/user/")` returns `"user"`, spec expects `""` for a trailing slash.
- "extracts filename from windows path": `expected C:\Program Files\app.exe to equal app.exe` — `get_filename` does not split on backslashes.
- "checks extension": `has_extension("archive.TAR", "tar")` is false — comparison in `src/lib/nogc_sync_mut/path.spl:123` is case-sensitive.
- "detects windows absolute paths": `is_absolute_path` is `path.starts_with("/")` only (path.spl:234 deprecated alias), so `C:\...` and `D:/...` are not absolute.

## Impact
The spec encodes the older merged `path_utils` contract (Windows-aware, trailing-slash semantics, case-insensitive extension). Current `std.path` is Unix-only with case-sensitive extension comparison, so any consumer relying on the old contract (cross-platform test-tree handling, docgen path scans on Windows trees) silently mis-classifies paths.

## Expectation
Either the implementation regains the documented contract (Windows separators in basename/absolute detection, trailing-slash basename -> "", case-insensitive `has_extension`) or the spec is deliberately re-scoped to Unix-only — that decision needs an owner; per testing rules the assertions were not weakened unilaterally.

## Unblock condition
A lane that decides impl-vs-spec direction for `std.path`; the four assertions are load-bearing contract statements, not typos.
