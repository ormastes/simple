# SimpleOS ARM64 Server Receipt Parser

Source: `test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl`

Evidence class: `host-fixture`. The parser consumes production receipt text;
the fixture does not manufacture live-guest evidence.

## Scenarios

- Accept complete filesystem-byte, reboot, shutdown, and credential-zeroization
  evidence.
- Reject a substituted HTTP body hash, missing fresh-process shutdown proof,
  duplicate fields, and an unverified target credential wipe.

The live ARM64 server gate remains authoritative for receipt production.

