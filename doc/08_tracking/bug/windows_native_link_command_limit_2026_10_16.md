# Windows native link object lists exceed CreateProcess limit

Observed with pure-Simple Phase 2 producer D6C3 and the phase4 test runner
entry: the saved link command contains 262 arguments and 47,525 characters.
Windows cannot spawn that command (32,767 character process command limit).
The link did not execute; this is not an unresolved-symbol diagnosis.

The MSVC linker boundary now writes `<output>.link.rsp` before invoking the
selected linker with one `@response-path` argument. Every original argument
is retained, including duplicate inputs and retained-symbol switches. Windows
CRT response quoting doubles backslashes before embedded/closing quotes.
The original `.link-command.txt` diagnostic remains unchanged; the response
file remains available after either outcome. A response write error stops
before spawning, and linker stdout, stderr and exit status retain their
existing failure reporting. No symbol policy is relaxed.

Focused unit coverage: empty arguments, spaces, embedded quotes, backslashes
before quotes, trailing backslashes, duplicate/order preservation, and a
response body larger than the Windows command limit. Execution qualification
and rebuilt-compiler test-runner qualification are pending; adding a spec
does not establish a passing runtime test.

Bug database reconciliation pending: this dated record preserves the concrete
failure while the qualified database tool is unavailable.
