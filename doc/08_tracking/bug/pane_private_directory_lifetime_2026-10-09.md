# POSIX pane launcher directory lifetime

The launcher previously unlinked its script and removed its private temporary
directory before executing the requested command. Parent cleanup retained the
directory name, allowing another process to substitute that name before cleanup.

The narrow repair retains the private directory until parent cleanup. The child
still unlinks its script. Script mode 0700, direct execution, existing PTY APIs,
and Windows launch behavior are unchanged. TMPDIR must permit execution.

## Verification

`test/01_unit/scripts/pane_launcher_lifetime_test.shs` passed on native POSIX
filesystem/process semantics in a bounded WSL run. It extracts the production
string helpers and launcher expression, directly executes the resulting script,
and checks literal and empty arguments, immediate standard input, retained
directory inode and mode 0700, refusal of symlink replacement, untouched victim
data, parent cleanup, a missing executable and a missing temporary parent. Its
negative control restores child directory removal and detects the lost directory.
Immediate cleanup is tested deterministically before script consumption, covering
the remaining-file cleanup case. Missing-parent creation uses the host primitive;
the application's relative-parent rejection is checked structurally.

This is emitted-shell-script verification, not Simple runtime or PTY integration
qualification. The retained Simple fixture
`test/fixtures/llm_caret/pane_posix_launch_probe.spl` adds assertions that the
directory remains reserved until pane close; that fixture remains **UNRUN**.
It covers full pane creation, input, failure, and immediate-close behavior when
an admitted POSIX Simple executable is available.

The broader argv/noexec candidate remains preserved at commit
`b09c1b755953e4dfff6a9dff08708042f0952de3`. It is deferred: the new runtime API
needs genuine C/Simple provider parity and full runtime/ABI and application
verification. Its extracted Unix-provider harness results do not establish that
qualification. This narrow repair neither adds that API nor claims noexec support.
