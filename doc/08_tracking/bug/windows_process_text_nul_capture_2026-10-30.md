# Windows native text capture truncates embedded NUL bytes

The corrected enum-RTI bootstrap producer failed source admission with
`truncated workaround Git status output`. The parser correctly requires the
final NUL from `git status --porcelain=v1 -z --untracked-files=all`.

The actual native route is `process_run_bounded` →
`process_capture_bounded_native` → `rt_process_run_bounded_tuple` →
`rt_process_run_bounded` → `win_process_run_capture`. Its text branch called
`process_timeout_result`, which recomputed captured lengths with `strlen`.
The byte branch and POSIX capture already used the measured lengths.

A real C capture probe against the retained 27-owner profile returned only
27 bytes and zero NULs, while direct Git produced 45,593 bytes with 808 NULs
and a terminating NUL. Evidence is retained at
`C:/dev/rti-process-text-probe-attempt2-20261030/run.result.sdn`.

Use measured stdout/stderr lengths in the Windows text branch. A synthetic
failure message still uses its own string length; exit status, timeout marker,
head/tail bounds, and byte capture remain unchanged. The regression exercises
embedded and final NULs on both streams through the array and native tuple
APIs, status 23, capped output, timeout, and a subsequent empty capture.

The focused native selfcheck passed with exit 0 and empty stderr after replacing
only the runtime_process owner. The source hash was
`C6B3908A283D608AFA872DFF6AF3ABDF7862D06B1A8F8BA9F23E8B3B2758A1BF`;
the test hash was
`15491B33A6B85012E45A5CED316CC68A45BB47791B714664E187C697948684A4`.
Evidence: `C:/dev/runtime-process-nul-fix-20261030/selfcheck.result.sdn`.
The retained compiler archive was not rebuilt. Canonical bug-database append
and the corrected producer's source-admission probe are separate pending checks.
