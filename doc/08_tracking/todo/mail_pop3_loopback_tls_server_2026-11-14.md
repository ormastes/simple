# TODO: pure-Simple loopback POP3 TLS/STLS fixture (blocked)

`test/01_unit/tools/mail_cli/fixtures/loopback_pop3_probe.py` was deleted (Python is forbidden).
Its 10 real-curl assertions (implicit TLS list/retr, auth rejected once, untrusted cert rejected,
dot-unstuffing, empty mailbox, LIST error, truncated RETR, STLS before credentials, STLS failure)
are now an in-development placeholder: `test/02_integration/app/mail_cli/mail_pop3_loopback_spec.spl`.

Blocker: Simple has an implicit-TLS server only (`rt_tls_server_create/accept/read_checked/write`,
`src/lib/nogc_sync_mut/io/tls_sffi.spl`, backed in the Rust seed runtime `net_tls.rs`). Missing:
(1) STLS upgrade of an accepted plaintext connection, (2) concurrent serve-while-client-runs in a
spec, (3) ephemeral certificate generation without openssl/Python.
