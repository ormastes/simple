# Live process capture paths were not quoted for both shells

Status: source fixed; Phase 2 native qualification pending.

Priority: P1. Host: aarch64-apple-darwin.

`process_run_timeout_live` inserted `TMPDIR` into a double-quoted child script
and single-quoted output redirections without escaping the path for either
shell. An apostrophe could terminate a redirection's quote, while a dollar
sign or backtick inside the child script could be expanded by the parent.
The requested worker then failed to run or wrote capture files elsewhere.

The owner now quotes the group path for the child shell, quotes the entire
child script as one argument to the parent shell, and independently quotes
the parent's stdout/stderr paths. The child expands `$$` only after the new
process group exists. The optional `stdbuf` branches and exit/timeout contract
are retained.

## Evidence and remaining gate

A bounded macOS `/bin/sh`/`POSIX::setsid` boundary experiment used a directory
containing spaces, an apostrophe, a double quote, a dollar sign, a backtick,
and a backslash. The old expansion failed the requested exit-7/output oracle
(the wrapper returned 0 without the requested capture). The new expansion
returned 7, preserved the exact quoted argument and both output streams, and
wrote a positive process-group identity. This exercises the shell boundary;
it is not evidence that Simple compiled or executed the changed owner.

`sh -n test/01_unit/scripts/macos_process_live_native_test.shs`,
`git diff --check`, and the working direct-env runtime guard passed.

The native harness now checks normal and unusual `TMPDIR` values with both
absent and present `stdbuf`, and requires all capture/group files to be
removed. The SSpec also checks the unusual path and nonrecursive directory
removal after the worker exits.

The admitted Phase 2 producer SHA256 is
`9aea8349b6fb411e46b325ecff70d2924173533d4c2e71d41e2619e9998c41a1`.
Its `test ... --mode=interpreter` command returns `error: unknown command
'test'`; neither the process SSpec nor SOSIX file-driver SSpec executed.
The native compile remains blocked by TODO 319's cold SCV inventory memory
growth, so it was not retried against the same known failing producer.
TODO 320 remains open for the final native assertions and RSS/time evidence.

## Independent expansion/newline regression, 2026-09-21

The production repair is already committed in `b8f75d62b4e`; the isolated
review at `6a7a22ddc37` therefore needed no additional production rewrite.
A bounded shell-boundary experiment evaluated the actual string literals and
`replace` expressions from that owner's launch construction, then executed
the resulting command through macOS `/bin/sh`. It compared the pre-fix owner
at `b8f75d62b4e^` with the requested source baseline. This evaluates the shell
construction only; it does not execute the Simple owner or its timeout loop.

The three directory cases were plain, the existing combined quote and
metacharacter case, and a name containing literal `$HOME`, `$(printf injected)`,
backtick command substitution, and a newline. Each ran with `stdbuf` absent
and with a transparent shim checking the `-oL -eL` arguments. The oracle
required exit 7, byte-exact stdout and stderr, and a numeric process-group ID
at the requested literal path. All six current-source cases passed.
The pre-fix quote cases returned 0 without the requested captures, and both
pre-fix expansion/newline cases returned 7 while failing the group-file
oracle. This demonstrates why checking only the worker exit code is
insufficient for this defect.

`test/02_integration/bootstrap/macos_process_live_tmpdir_expansion_spec.spl`
adds real process assertions for the expansion/newline directory, group-file
presence with the worker's exact PID, byte-exact argument round-trip, both
captured streams, exit status, environment
restoration, and nonrecursive temporary-directory cleanup. Its execution
remains part of TODO 320's native qualification gate; shell-boundary success
does not close that gate. A separate bounded run of the new spec's exact worker
script against both shell constructions rejected the pre-fix owner with
exit 91 (missing group file) and accepted the current owner with exit 7 and
the expected streams. This validates the new oracle without claiming that
the Simple SSpec itself executed.
