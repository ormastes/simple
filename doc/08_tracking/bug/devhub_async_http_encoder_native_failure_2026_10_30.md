# Async HTTP client duplicate encoder blocks native DevHub

Status: OPEN. Owner: Codex Astra (claimed before source edits, 2026-10-30).

The retained actual DevHub build at source snapshot
`4485c17166cc115edb617cee5dff12a5dbec0334b8bba1f49a7c5615ad69acfb`
failed with unresolved `to_string` at
`src/lib/nogc_async_mut/http_client/types.spl:57:23`.
The duplicate URL encoder mixes codepoint traversal with byte length and invokes
an unsupported radix overload. The same family's `http/url.spl` already owns
UTF-8 byte percent encoding. Repair by delegating to that owner, preserving
the HTTP client API and configured library family.

Exact build evidence: `build/devhub-release-dev-20261030/native-build.stderr.log`.
Adjacent regressions cover reserved ASCII, empty/unreserved input and UTF-8
octets through direct and component APIs. Native validation pending.

This is separate from the same build's unsubstituted generic `T` diagnostics.
Removing this encoder defect does not establish a working DevHub executable.

Native regression verified 2026-10-30: pinned Phase 2 build exited0, executable exited0 and ran five actual-value cases. Executable SHA256 `45495f4cf9f40eff6428c14d54645f69b3a22bc3aaa74088cb9746c3331e06a2`. Evidence: `build/devhub-release-dev-20261030/focused-url-encode-run2/corrected-result.sdn`. Original result.sdn remains FAIL because the harness expected the wrong PASS label; corrected receipt binds actual source/stdout without rerunning. This proves the focused encoder repair, not full DevHub readiness. Status remains OPEN until reviewed fix lands.
