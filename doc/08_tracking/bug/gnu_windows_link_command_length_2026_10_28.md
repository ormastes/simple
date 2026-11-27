# GNU Windows linking exceeds CreateProcess command-line length

Tracking key: BUG-GNU-WINDOWS-LINK-ARGV-LIMIT-20261028.
Canonical BugDB insertion is pending its existing malformed-data blocker.

The full 292-module Phase2 runner build reached linking under GNU Clang with
an original recorded command of 52,202 bytes. Direct spawning failed with
Windows error 206 before the linker executed. Producer SHA256:
`8365cec04eb7292695e9e10850af68c0dab61e86a5bacae5ad5d3e51f0183f60`.

Evidence: integration lane
`build/phase2-descendants-20261028/runner-extern-linkage-cap14/`.
The complete original argv text and failed-link inputs remain retained.

GNU executable and DLL link paths now write ordered response-file arguments
and invoke the selected GNU Clang driver with `--rsp-quoting=windows` and the
response path. They reuse the existing pure-Simple Windows argument encoder.
No MSVC executable, runtime provider, or SDK is introduced. Original full argv
records remain unchanged. NUL arguments and failed writes prevent spawning;
response files remain available on success and failure.

A diagnostic control encoded the actual retained command with that Windows
encoding. Clang accepted the transport and reached LLD, which reported six
generic extern symbols from the separate archive-replay defect. Thus transport
was demonstrated, but this diagnostic link did not produce a passing runner.
Evidence: the same attempt's `response-control/` directory, including response
bytes, original-command digest, argument count, link status, and stderr.

The production source fix still requires a rebuilt producer, Hello execution,
and a successful real long-command runner link. A Hello output path containing
spaces will check response-file path and output-argument quoting as part of
the new producer's qualification. No current production verification PASS or
canonical admission is claimed.

## Production transport evidence

The final a7578958 producer built and executed Hello with a path containing
spaces. The real full-runner native link also completed through the production
GNU Clang response-file path. This supersedes the pending transport check above.
The subsequent separate SMF cache phase exceeded the 16 GiB cap; no final
runner publication or overall verification PASS is claimed.
