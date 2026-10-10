# Web TLS helper imports and missing SHA256 facade alias

Status: OPEN; source repair and regressions AUTHORED_UNEXECUTED.

Producer1fcd9a20 (873ea2e4 compiler source) building frozen29223ded5
Web closure failedHIR with75 diagnostic records in17files, exit1 after162.29s.
Named-payload errors from the preceding165-record closure no longer occur.

TLS record/handshake/cipher and configured IO consumers call helpers without
importing their canonical owners. In addition the syncTLS utility facade exports
`tls_sha256`, while existing asynchronous facades and handshake callers request
`sha256`. Exactimports and a canonicalalias `tls_sha256 as sha256` repair these
source contracts without changing algorithm bodies or configured routing.
Original `tls_sha256` export remains available. No host/runtime shortcut is added.

Two scenarios/four real digest assertions use standard empty-input and `abc`
digests through original/alias and configured async families. Native fixture:
`test/fixtures/lib/tls_canonical_sha256_alias/main.spl`, two executable checks.
Fixture results and full Web/core/MCP qualification remain pending. Native
MIR may expose existing untyped helper limitations; retain those failures.
Other Web errors (_make_j0/_inc32 local calls, mutex keeping helper, chr and
collection method ownership) remain separate; this repair does not claim them fixed.
