# BuildRunner publication creates parents before containment validation

Baseline: release/1.0.0 `b7c1d4d7cde`. Date: 2026-10-29.

Publication called recursive directory creation before validating the resolved
output parent. With `output/escape` pointing outside the output root, publishing
`escape/new/deep/hello` created `new/deep` in the external directory before the
containment check rejected publication. Returning false did not undo the write.

Publication now validates the relative path and walks its parent components.
It validates the output root, creates only the next missing directory, and
checks that directory's containment before advancing. Existing symlinks that
resolve outside the output root are rejected before any child creation. The
existing Windows reparse-directory checks apply at each step. The final
publication checks remain in place. As before, the manager must own the roots
and their ancestors; this does not establish protection against hostile
concurrent directory replacement.

The regression failed against the baseline: 5/6 focused tests passed, with the
escaping-parent test observing an unwanted external directory. After the fix,
6/6 passed, including nested output creation and all cached-mode scenarios.
Logs: `/private/tmp/buildrunner-parent-red.log` and
`/private/tmp/buildrunner-parent-green.log`.

The adjacent CLI output-root specification passed 3/3, including cache repair
and read-only verification (`/private/tmp/buildrunner-parent-cli.log`). The
working-tree direct-environment guard and whitespace check passed; no
executable specs exist under `doc/06_spec`. Execution was on Darwin arm64;
Windows behavior has not been executed in this change.

Tests reused the existing pinned Phase 1 interpreter, SHA256
`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`,
with `SIMPLE_LIB=src` and
`test SPEC --mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon --sequential`.
These are source-interpreter publication checks, not native BuildRunner Hello
or provider admission evidence. No compiler was rebuilt and no V4 capability
or containment guard was changed. Native manager compilation and Darwin V4
descendant ownership remain outstanding.
