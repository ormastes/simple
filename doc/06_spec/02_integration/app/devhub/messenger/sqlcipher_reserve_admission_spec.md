# SQLCipher4 reserve admission

Status: AUTHORED_UNRUN. Authored manual, not docgen output.
The SQLCipher-specific reserve guard is repaired in source. Execution remains UNRUN; no Simple RED or GREEN result is claimed.
Proof class: independent .NET fixtures through production storage admission.
Coverage: UNMEASURED. No 99% claim, no runtime admission, no generated zero-stub claim.

Spec: `test/02_integration/app/devhub/messenger/sqlcipher_reserve_admission_spec.spl`

Spec SHA-256: `ebbf2b3175b38823a8e42636c02f3c7aa426b396fa4e34df2f6e77069a21d775`

## Flow

1. Hash each committed independently encrypted 4096-byte page before opening.
2. Open through the production SQLCipher storage port using the synthetic public
   SecretRef. Require successful reserve-80 admission and close its plaintext view.
3. Require `STORAGE_PORT_CORRUPT_SOURCE` for authenticated reserve 0, 79 and 81.
4. Require `STORAGE_PORT_AUTHENTICATION_FAILED` when reserve 79 also has a bad tag.
5. Open the independent plaintext SQLite reserve-zero fixture and require
   reserve zero admission (REQ-CIPHER-RESERVE-003).

REQ-CIPHER-RESERVE-001 enforces agreement between decrypted header byte20 and
fixed 80-byte codec reserve. REQ-CIPHER-RESERVE-002 discriminates authentication
from structural validation using the same malformed header with a damaged tag.
This demonstrates observable error precedence; it does not instrument whether
CBC was called, nor prove constant-time execution.

The independent producer uses .NET PBKDF2-HMAC-SHA512 (256000 then 2 iterations),
salt XOR0x3a, AES256-CBC with Padding=None and HMACSHA512 over ciphertext+IV+LE32.
Fixtures are synthetic single-page empty-schema headers, not upstream SQLCipher
exports or production Messenger data. All passphrase/key material is public.
The plaintext reserve-zero control uses usable size4096 and passed independent
Python SQLite integrity_check after correcting its empty-leaf content offset.
That fixture check is not Simple regression execution.

- `test/fixtures/database/sqlcipher4/gen_reserve_fixtures.ps1` SHA-256 `1dd37d2369622421bb00441a2bad8d9e90459456423535d659de4174b8016ec4`
- `test/fixtures/database/sqlcipher4/reserve_fixtures.sdn` SHA-256 `f68ca285201a640506119b98c0129e74008c381f8bb0ad7fd1fb6b44baf0019e`
- `test/fixtures/database/sqlcipher4/reserve_0.sqlcipher4` SHA-256 `157ad55f79babb074617a3b3b6fe795c45f6c79dd0745f4ed26cbb42f01ebeca`
- `test/fixtures/database/sqlcipher4/reserve_79.sqlcipher4` SHA-256 `c800d459c228ce9350e615ca99c693a9c573301240f6049f1b8098a00f8e0acb`
- `test/fixtures/database/sqlcipher4/reserve_80.sqlcipher4` SHA-256 `ed4c8327164ae447dd3c7dddd9d87b00edef702aa2a70a5d9decdfffb46023a4`
- `test/fixtures/database/sqlcipher4/reserve_81.sqlcipher4` SHA-256 `3c2db043c9e0b0666bfe348dd20c03995be2383984f8f07db3f49aa64718bd50`
- `test/fixtures/database/sqlcipher4/reserve_79_bad_tag.sqlcipher4` SHA-256 `d8c7b8821e62d953f1e09cf9b7ee4dca594301cf37c251c7f7214a96ba279992`

Plaintext control: `test/fixtures/database/sqlcipher4/reserve_0_plain.sqlite` SHA-256 `cb2a842f5e03920b74f948284638e14d2254c781f6bf319e1b44e5f625efc165`

## Reference and admission limits

Pinned SQLCipher v4.6.1 source commit c5bd336ece77922433aaf6d6fe8cf203b0c299d5,
`src/sqlcipher.c`, SHA-256 010d418c541cd3606f58fd705ae404201fd243fd20cb387439697289a6c87219:
`sqlcipher_page_hmac` and `sqlcipher_page_cipher` bind IV/page number and verify
authentication before the cipher provider. SQLCipher profile source and official
API snapshot pin 4096-byte pages and 80-byte reserve for SHA512. NIST SP800-38A
section6.2 defines CBC. See the campaign supplemental_sources.md for full pins.

After a qualified runtime exists, run the spec and retain failure/success logs,
then generate the manual using spipe-docgen with zero stubs. Runtime checks,
source matched branch counts and docgen remain unexecuted.
