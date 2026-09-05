# Web request-port evidence authenticity gap

Status: open. The `web-server-request-port` must-check row remains `TODO`.

The current generic external receipt can authenticate a reviewer's signature,
but a proposed lane-specific producer was rejected because it accepted an
arbitrary executable and source file, trusted producer-authored lifecycle
claims, and did not retain kernel-observed proof that the request and response
bytes crossed the server-owned loopback socket. It also allowed unsafe output
paths and did not bind a clean Git source closure through canonical Stage 4 to
the executable under test.

The next implementation must use a new versioned acceptance contract while
preserving legacy v1 receipt parsing. It must:

- select a declared committed production entry (candidate:
  `test/fixture/net/simple_http_server.spl`, or a separately approved app
  entry), require its relevant working-tree sources to equal `HEAD`, and build
  it with the retained canonical Stage-4 compiler/provenance in a closed
  environment;
- retain the exact build recipe, source closure, compiler/version, provenance,
  and executable hashes;
- retain server-received request bytes and client-received response bytes plus
  kernel-observed accept/read/write evidence bound to the server PID/socket;
- use monotonic timestamps for readiness, request, response, stop start/end,
  and enforce bounded stop, no descendants, and no remaining listener;
- write only to a fresh, repository-contained directory with no symlinked
  ancestors; and
- emit an unsigned bundle which is authenticated before any attachment is
  loaded or executed. The producer must not sign or promote the ledger row.

Direct handler calls, shell/`nc` fixture servers, arbitrary caller-supplied
executables, and producer-authored PASS counters are not production evidence.

