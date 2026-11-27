# Owned daemon poll diagnostic: unresolved secure-memory methods

Status: OPEN diagnostic dependency, report-only. No bug-db row mutation.
Producer SHA256: `afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`,
unadmitted pure-Simple compiler, LLVM/CoreC on aarch64 Linux.

Entry: `test/fixtures/native_daemon_owned_poll_v1/main.spl`. It selects actual
SDK idle/stopped, owned publication-failure and legacy publication-failure
oracles; successful acknowledgement and its known hash failure are excluded.

Two authorized builds exited 1 before linking:

- `094cafa9524`: 100-module closure. The fixture imported `std.spec.fail` only
  to reject a forbidden callback.
- `13709568c52`: equivalent built-in `assert(false)` removes that test
  dependency. Compatible private caches are retained; closure drops to 71.

Both first failures are MIR lowering of `lib.common.crypto.secure_memory`:
unresolved `fill_span`, receiver type absent, at source lines 57, 78, 94 and 106.
Production `daemon_sdk.lock` also reaches this module through the checked
entropy facade `io.crypto_sffi` and `common.crypto.sha256`. Removing the SSpec
import does not remove that path. This is not evidence that the new generic
owner-return method failed, nor evidence that it works.

The second module-failure record binds snapshot
`aa312f500d99625c5fea686d041e3b7bca809b65feba41cf9c384fa77cbed1e9`.
Its cached first-error text retains the earlier snapshot path
`95c977c238cbd45ae0c7a7d72c4060c5b43659472460ba9ab6a5f2da374bd6d3`;
both records are retained. All fixture/SDK input hashes checked unchanged
after each build. Aggregate failed-module counts are not independent bugs.

Evidence resides in `build/daemon-owned-poll-native/` in the isolated daemon
worktree: `build.log`, `build.exit`, `build-v2.log`, `build-v2.exit`, both input
SHA256 manifests and private HIR/frontend/native caches. Builds used one thread,
no stub fallback, private TMPDIR, 360-second process-group timeouts and 8-GiB
tree limits. No executable exists and no runtime test ran. Stop unchanged
retries; resume requires independent compiler-owner evidence or an updated
producer. No product stub, cryptographic weakening or alternate daemon loop
was introduced. Admitted SSpec/core/MCP checks remain NOT_RUN.
