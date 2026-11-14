# TODO: POP3 loopback STLS upgrade fixture (blocked)

The 8 implicit-TLS scenarios of the deleted Python probe now run in pure Simple:
`test/01_unit/tools/mail_cli/fixtures/loopback_pop3_server.spl` (rt_tls_server_*) driven by
`loopback_pop3_probe.shs`, asserted by `test/02_integration/app/mail_cli/mail_pop3_loopback_spec.spl`.

Remaining (2 scenarios, one fail-fast `it` in that spec): STLS before credentials, and STLS failure
sends no credentials.

Blocker: Simple has an implicit-TLS server only (`rt_tls_server_create/accept/read_checked/write`,
`src/lib/nogc_sync_mut/io/tls_sffi.spl`, backed in the Rust seed runtime `net_tls.rs`). Missing:
upgrade of an accepted plaintext connection to TLS mid-stream (STLS). Once it exists, add a
`starttls` mode to the server and the two scenarios to the probe, then drop `@tag:in-development`.
