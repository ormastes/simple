# DevHub secured Messenger DB key-session open failure

Status: OPEN. Severity: P1. Date: 2026-10-27.

The fresh secured DB ledger1 build passed with the existing Phase2 compiler, but actual execution failed at direct key-session open before encrypted decode. The memory oracle passed NIST AES, independent KDF/HMAC, SQLite integrity, rows and overflow checks. The encrypted inputs and metadata stayed unchanged and no plaintext or journal secret files remained.

This is the main DevHub Messenger database feature blocker, not an infrastructure exemption. The exact cause remains unisolated. Repair key-session open first; then qualify secure SQLite decode, snapshot lifetime and efficient bounded paging with independent row oracles and memory-only plaintext. Do not claim DB support from the memory oracle alone.

Evidence: `D:/dev/simple-devhub-secured-db-p2-20261027/build/devhub-completion/fresh-secured-db-ledger1-build.log` and `fresh-secured-db-ledger1-run.log`. Ledger1 build exit0 / run exit1. No additional DB feature experiments in this session.
