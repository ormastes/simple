# Bare `duplicate-check` exited successfully without checking anything

- **Status:** OPEN — bounded fix experiment removed after final review found a flags-only bypass.
- **Reproducer:** `simple duplicate-check` printed usage and exited `0` before reaching argument validation, so automation could report a vacuous clean result.
- **Cause:** `run_duplicate_check` returns usage/0 for truly bare argv, while `target_path_from_args` silently defaults to `src/`. Checking argv length alone is insufficient: flags-only input such as `--format json` also has no positional path and would reach the implicit full-repository scan.
- **Root fix:** make positional target extraction return empty/optional when absent, process explicit help first, then require the target with usage/2 for both bare and flags-only invocations. Update every active help surface from `[path]` to `<path>`. Explicit `--help` and `-h` must remain `0`.
- **Why no implicit `src/` scan:** the semantic default can traverse the full repository and is unsuitable as an unbounded bootstrap sanity action. The essential-tools smoke already uses bounded calibrated fixtures.
- **Required regression:** cover bare, flags-only, explicit-help, and explicit-path argument shapes without starting a repository scan. Two heavy owner-spec attempts timed out in compiler diagnostic flood; a lightweight source contract passed but missed the flags-only bypass and was removed.
