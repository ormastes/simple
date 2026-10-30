# Secured Messenger DB blocker registration

The secured DB main feature remains blocked: fresh ledger1 compiled but returned Err at direct key-session open before decode. Its memory cryptography and SQLite oracle passed; those results do not establish working Messenger DB access. No further feature experiments were run.

Registered OPEN P1 bug `devhub_secured_db_key_session_open_failure_2026_10_27` and blocked TODO `377`. The TODO requires key-session repair followed by secure SQLite snapshot and efficient bounded paging qualification. Both link the bug report and preserve the unresolved status.

One metadata-only native utility was compiled with the existing Phase2 producer, without rebuilding the compiler. Astra reviewed the narrow TODO append API with no P0/P1 findings for these records. The API holds the database lock, refuses a nonempty WAL, checks an existing CRC when present, serializes only the new row through SdnTable and publishes atomically. Existing TODO data was unsealed; publication adds a valid CRC while preserving its entire old body. The two database writes are separately atomic, not a cross-file transaction.

The utility compiled and ran exit0 against isolated copies first. An independent Python zlib audit then required exact original body bytes after removing only the new-ID rows and checked every TODO field. Actual input bytes were rechecked against those backups before one actual API run, which exited0. Actual output matched the qualified copies.

| Database | Preserved old rows | Added rows | Unsigned CRC32 |
| --- | ---: | ---: | ---: |
| Bug | 5299 | 4 | 367800804 |
| TODO | 367 | 1 | 2283810727 |

Bug SHA256: `dc58fdeafbb26b072811d35448bd79caa2d7c0d576bbac6aaa7baca69b4c9443`.

TODO SHA256: `2f8d439c0755304927b07b2d9fe6728baec4e2fec6596263281e92e6f06a71c1`.

Producer SHA256: `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.

Metadata artifact SHA256: `22030d9e03036af2cd2320caa7a42660e41519ffa0d2de633205519a9518c24e`.

Local evidence: `build/devhub-completion/secured-db-tracking-evidence.json`, `secured-db-tracking-build.log`, `secured-db-tracking-copy-run.log`, `secured-db-tracking-actual-run.log`, before-image backups and `verify_secured_tracking.py`. This is metadata-registration evidence, not a full SSpec or Messenger feature PASS. No hand-edited registry rows, checksum repairs, generic full saves or derived-index changes were used.
