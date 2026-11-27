# Structured Windows PTY launch admission

Status: **NOT_RUN**. This manual was authored alongside the executable SSpec;
it is not generated execution evidence. Doc generation and review remain pending.

Source: `test/01_unit/lib/io/windows_pty_launch_config_spec.spl`.

| Requirement | Scenario and expected observation |
|---|---|
| REQ-WPL-001 | Exec produces independently quoted executable/arguments. Empty arguments, spaces, embedded quotes, trailing backslashes and Unicode remain distinct. Shell operators and `%PATH%` remain argument text. |
| REQ-WPL-002 | Shell preserves caller command text inside the explicit `cmd /D /S /C` wrapper; it does not apply CRT argument quoting to shell syntax. |
| REQ-WPL-003 | Admission accepts Unicode cwd, Unicode environment names/values, empty Set values and case-varied Remove names. |
| REQ-WPL-004 | Public Set and Remove reject hidden drive names containing `=`. |
| REQ-WPL-005 | Admission rejects embedded NUL, empty explicit cwd, excessive argument count and a fully quoted command exceeding the UTF-16 bound. Supplementary scalars count as two UTF-16 units. |
| REQ-WPL-006 | Strict byte validation rejects overlong, truncated, surrogate, out-of-range and stray-continuation UTF-8. Quoting preserves malformed raw bytes for rejection, internal environment NUL separators remain valid, and a near-1MiB multibyte value retains the existing allowance. |

These assertions cover pure preparation rules. They cannot establish native
CreateProcessW behavior, environment merge/case rules, Job ownership or cleanup.
Those require the actual-child scenario described in
`doc/09_report/coremux_windows_pty_launch_source_2026_10_25.md`.

Correction cycle 2 authors 13 cases in total. None has run. The native scenario
keeps its strict requirement for both successful `close` and independent cleanup
proof after missing executable/cwd failures; the production owner was corrected
instead of weakening that oracle. Native strict-wide rejection and exact
NUL-separated UTF-16 output were added to the actual-child fixture.
