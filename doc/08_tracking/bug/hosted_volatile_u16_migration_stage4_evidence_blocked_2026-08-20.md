# Hosted volatile-u16 migration Stage 4 evidence blocked — 2026-08-20

## Status

HOLD. The pure-Simple hosted owner and ABI-preserving facade migration are
implemented, but the available `bin/simple` identifies itself as a Rust-built
bootstrap seed. It cannot provide admitted current-source Stage 4 acceptance.

## Implemented boundary

- `std.io.hosted_volatile_u16_device` privately owns bounded addresses/values.
- Admission creates a private TLS handle/capability; every transition rereads
  canonical logical-thread TLS and rejects non-creator access.
- Unknown addresses and unowned threads fail closed; values normalize with
  `value & 65535`; the read rejection sentinel remains ABI-compatible `-1`.
- `volatile_ops` routes admitted hosted u16 calls to the Simple owner. Native
  callers retain `rt_volatile_read_u16(i64)->i64` and
  `rt_volatile_write_u16(i64,i64)` unchanged.
- Rust interpreter u16 provider definitions and registrations are removed.

## Diagnostic evidence (not Stage 4 acceptance)

- Both changed Simple modules pass focused `check` under the available seed.
- Source guards find zero Rust interpreter u16 definitions/registrations and
  retain both native runtime ABI definitions.
- The production facade probe passes all 31 decision/output rows. Its output
  is byte-identical to the frozen C oracle, SHA-256
  `c7d64e59ed4348b674641348862f235f552db8977e595afe4c7270be6eeb02a1`.
- C/Simple performance probes produce the identical checksum `64998792640`
  (SHA-256 `b73c53bc18ead34099af7caf5977f3a847a820b1aab2c46305f37170f982945f`).
  Seed measurements were C `0.01s` versus Simple `0.58s` and therefore do not
  meet the intended `<=3x` native threshold or constitute comparable native
  evidence.
- Focused SSpec cycle 1 reached the inherited runner defect: expected final
  generation 71, observed 73 after the cross-thread probe. The standalone
  production probe reports the correct 71. No retry was made.

## Required continuation

Using an admitted current-source pure-Simple Stage 4 runtime, run each once:
100% decision/branch coverage, focused mutation kills, compiled C/Simple parity,
and warm native performance medians. Until those rows pass, component verdict
remains HOLD and the broader envelope must not claim GO.
