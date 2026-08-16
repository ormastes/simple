# Secure Pure-Simple servers: evidence status

Date: 2026-08-16 (continuation audit; historical runtime observations remain
dated 2026-08-14)

Parallel recovery follow-up found that the synchronous response serializer
emitted canonical framing and then appended conflicting application framing
fields. The scoped source repair now owns `Content-Length`,
`Transfer-Encoding`, and `Connection` at the writer, rejects non-token field
names and control-bearing values, preserves safe default security headers, and
adds direct plus real-loopback wire oracles. Independent static review cycle 2
accepted the patch. No admitted Stage-4 CLI or adjacent provenance receipt
exists locally, so this is code-only evidence and promotes no AC.

## 2026-08-16 continuation audit

The detached baseline audited for this continuation was
`00496db6f95a12dfc7d7c0ecd21648093be61322`, equal to the then-local
`origin/main`. No build or test ran in the documentation lane.

That baseline contains the later `std.common.net.http_core` extraction, so the
synchronous parser/router no longer exclusively own header/body policy, path
safety, or route matching. The retained green counts attached to that
extraction used a runner with a seed-banner caveat and do not prove this lane on
an admitted Stage-4 CLI. Static audit also found that the synchronous wrapper
accepted non-chunked `Transfer-Encoding` after the extraction and that its
canonical writer lacked a response-byte/write-all boundary.

Bounded sidecars prepared, but did not execute, these continuation changes:

- synchronous rejection of every non-empty unsupported transfer coding;
- a positive `SecureServerPolicy.max_response_bytes`, complete bounded response
  (or hardened 500) selection, and `write_all` production writes;
- byte-compatible DB argument slicing plus an adjacent quoted multibyte oracle;
- a real ephemeral-loopback DB bind/OPEN/EOF/session-cleanup/close/rebind
  fixture, including explicit-stop rebind.

Fresh highest-capability review cycle 1 rejected the initial handoff because
retained listener copies could double-close the raw fd and the idle-stop oracle,
canonical DB steps, and current mirrors were incomplete. The mirrors and
scenario shape were corrected, but re-review required a stronger owner boundary.

Re-review cycle 2 found that close-once did not itself publish stopped state
and that a sleep-only idle test could pass before the worker reached accept.
The working tree now keeps only a scalar listener lease/terminal receipt behind
the shared mutex, serializes bounded accept and close around owner-local
listener values through that gate, and gives the stopping
domain only `DbStopControl`. The idle scenario observes its shared
accept-attempt receipt before stop/join/rebind. Review cycle 3 then found that
a connection completing during the in-flight accept could still reach request
dispatch. The final bounded fix rechecks stop after accept, closes that transport,
and adds an empty-response/zero-state oracle. This remains unexecuted code-only
evidence; the three-cycle cap is reached.

Post-rebase triage used two mutable `/tmp` logs produced by a Rust seed only as
diagnostic clues. Those logs are not admissible receipts. They localized the
DB failures to a class-valued mutex payload becoming nil and a stale
`ServeOutcome` assertion, and the SimpleOS failure to assertions for a retired
noalloc allocator path. The source now uses a scalar mutex lease around the
owner-local listener, checks the returned outcome, removes the dead RISC-V
allocator declaration, and asserts the bounded aligned bump-heap contract.
Independent repair review cycle 1 accepted these corrections with no blocking
source finding. They remain code-only until the exact Stage-4 commands pass;
review acceptance is not runtime or release evidence.

They are code-only handoff material, not PASS evidence. AC-9/10/12/13 remain
open. Existing manuals are hand-authored rather than current docgen receipts;
current `sspec-maintain` scorecards, deliberate-red calibration, focused
Stage-4 results, and highest-capability review remain absent. The exact
once-only deferred sequence is
`doc/03_plan/sys_test/secure_pure_simple_servers.md`.

## Temporary staged-runtime provenance

The strongest current-source staged artifact found in this worktree is
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`:

- SHA-256: `5883722a6cafd17006ecab001e714e9e43774014bf44b1af459a92bd142099f5`
- ELF Build ID: `9db2d66edbf77fc3fd0674f3cc21ae4062a2b6ec`
- Size: 131,026,208 bytes; version: `simple-bootstrap 1.0.0-beta`
- Producer receipt:
  `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-command.transcript`
  records LLVM with `core-c-bootstrap`, `SIMPLE_BOOTSTRAP=1`,
  `SIMPLE_NO_STUB_FALLBACK=1`, and entry `src/app/cli/bootstrap_main.spl`.

This is a self-hosted Stage-2 bootstrap compiler, not an admitted Stage-4 full
CLI. An unverified operator observation says one `check` and one focused web
`test` probe returned `unknown command`. The artifact is retained as provenance
and that observation as a diagnostic negative only; neither can
credit a requirement, SPipe execution, docgen, or release gate.

Unverified operator observations say one bounded Stage-2 `native-build` was
attempted for each focused lane. The web
spec stopped in HIR (`ANY` field `error?` could not be inferred); the DB spec
reached link and lacked `core-c-bootstrap` symbols `rt_file_create_excl`,
`rt_file_sync`, and `rt_crc32_text`. Neither produced an executable, and no
variant was retried.

Unverified operator observations from the explicitly authorized bootstrap-seed
diagnostic then ran the DB specs
(seed SHA-256
`c9321d38fa7623008e185289bc9dc193489ab490f7ec238b9a3cadcd0b4788ea`):
durability 22/0. After bounded test-only corrections, secure server reached 7/0
and tier server ended 39/1; its remaining RED is UTF-8 batch round-trip (`猫`
became replacement characters), and the three-attempt cap is exhausted. These
commands have no retained immutable command receipts, so no acceptance credit
is taken. The continuation source audit attributed the parser defect to mixing
the byte offset from `index_of` with `chars().len()` as a slice endpoint and
prepared a byte-compatible correction plus adjacent oracle. That correction is
still unexecuted, so the historical RED is not converted to PASS. This seed
evidence is bootstrap diagnostics, never production or admitted Stage-4
verification.

Sibling `restart12-*` worktrees expose the same deployed wrapper hash
`714e1e8e43474413b8c0b82cb561bc8585462e3539417e2c8dd883ea470fc736`
and the same `simple_native` hash
`7fc570189e1d689c8c99988981a4766b0a42ba9a70dc97571c71d2a75c46823b`;
they are not stronger independent candidates. No sibling staged artifact with
a full verification command surface was found.

## Authored, statically reviewable evidence

- `secure_pure_simple_db_server_spec.spl` calls the production `listen` entry
  point only for deterministic pre-bind rejection of zero connection capacity,
  then asserts listener/connection state remains released.
- `db_durability_spec.spl` covers the P3/P4 crash boundary and a reconnect retry
  using a durable, principal-bound commit receipt. Cross-principal and
  different-content reuse are explicit conflicts.
- DB capability coverage includes read-only, empty-grant, wrong-table,
  missing-table, write-only, and data-operation denial cases.
- Missing, wrong, and unknown credentials are checked against one exact
  `ERR code=auth msg=authentication failed` frame.
- The tier spec source contains an injected isolation violation plus
  unconditional controls, so static review finds a non-placeholder oracle;
  deliberate-red execution remains uncredited.
- Mirrored manuals exist for all three DB system specs.

## Release-blocking evidence not available

No admitted Pure-Simple Stage-4 CLI is healthy. Consequently no admitted
Stage-4 runtime executed or credited the DB specs or live-listener scenario,
and this lane did not run `sspec-maintain scan` or `spipe-docgen`; it did not
produce a genuine deliberate-red failure/restoration
transcript, runtime coverage, socket transcript, or `0 stubs` generator
receipt. Hand-authored manuals are not represented as generated provenance.
The secure web scenario's manual-step and boolean-wrapper quality findings were
corrected in the unexecuted working spec, but a fresh maintenance scan and
generated-manual review are still required before AC-10 can pass.

A live listener PASS is intentionally absent. The continuation fixture now
binds an ephemeral loopback port, prequeues a real client, exchanges a framed
`OPEN`, observes EOF cleanup, closes, and proves normal/explicit-stop rebind.
It deliberately avoids both a connector-free blocking accept and the old
vacuous "any bind error" shape. Until that fixture executes on the admitted
runtime, the real bind/accept/EOF/stop row is RED/BLOCKED, not skipped or passed.

Production and scripted drains now share `bounded_message_response`, and the
focused source scenario constructs an oversized encoded result. Runtime TCP
wire evidence remains RED/BLOCKED; structural sharing is not a socket transcript.

AC-9, AC-10, AC-12, and final-review AC-13 remain open. Production TLS remains
separately blocked by GAP-TLS-3. Static source shape cannot prove actual socket
accept/cleanup, scheduler exclusion across P3/P4, fsync/rename crash behavior,
or lost-ack replay behavior; those require the healthy admitted runtime.
