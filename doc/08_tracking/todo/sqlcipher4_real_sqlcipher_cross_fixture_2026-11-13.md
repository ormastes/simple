# TODO: SQLCipher 4 fixture produced by real SQLCipher

Status: open (2026-11-13)

Every committed SQLCipher 4 fixture under `test/fixtures/database/sqlcipher4/`
was produced by an in-repo generator (python `gen_*.py` with its own
NIST-checked AES plus hashlib PBKDF2/HMAC, or .NET `gen_reserve_fixtures.ps1`).
`test/01_unit/lib/database/codec/sqlcipher4_independent_oracle_spec.spl`
proves the Simple stdlib and the python generator agree on every algorithm
step, but both were written from the same reading of SQLCipher 4, so a shared
misreading would pass.

Needed: one small database created by the real `sqlcipher` CLI (4.x defaults,
`PRAGMA key = '<passphrase>'`, plus one `x'<64 hex>'` raw-key database), with
the passphrase, the salt and the table contents written down, committed under
`test/fixtures/database/sqlcipher4/real/`, and a spec that opens it through
`storage_backend_sqlcipher4_open` and checks the rows exactly. Raw-key mode is
rejected today (`SQLCIPHER4_UNSUPPORTED_KEY_TYPE`) until such a fixture exists.
