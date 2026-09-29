# Slang physical paged-KV activation evidence

Date: 2026-09-09

Status: implementation qualification evidence; final release verification is
still blocked on an admitted x86_64 pure-Simple check/docgen worker. No speedup
or memory-saving claim is made.

## Immutable inputs

- Simple base revision: `d6c815ea28b2d575c594ad647b04ca55799e67cd`
- Uncommitted worktree diff SHA-256 at measurement:
  `4546038a0b395399ad7d118cf33cb2d71b7b9e528c44ae5885c5b40a27e2fc93`
- llama.cpp fork revision: `ed1bb5cff60be3b9045d4465420c344833492054`
- Model: `stories15M-q4_0.gguf`, SHA-256
  `6151b1929d7f5aa3385d9ddef3393e55587c0a55de661562322bc51dfda93a04`
- Diagnostic release driver SHA-256:
  `20190ce341c01edf82ba4c98a1be6879f1cd366314bd06fa2670c8ad5898f97d`
- Provider shim SHA-256:
  `18fbae63e007719c9e04266f45f30afb160c2171dc34fbc374c035748c794d99`

The driver is a Rust-built diagnostic artifact containing the current compiler
fix. It is valid for the focused interpreter/runtime qualification only; it is
not Stage 4 or final release evidence.

## Source identities

- `page_contract.spl`:
  `6edaefcd00eafee5eab34429412a6a05834cc6638db8fbe3b7a05cb9beeea401`
- `page_manager.spl`:
  `64ca8005919eb0358706e1e734e5e5331bff6ead91fc3d7e1e2c574370f1a789`
- `paged_executor.spl`:
  `45c62bff09a25db839038ad7680c7f36fb0f97490ba6ca26e089c755663a5aa6`
- Simple-owner fixture:
  `0461a9d7eb9c355e6dfc07c7a4e8323a5dc17078ee77c7fa90d1f8e3b5cd0c92`

## Observed result

One process loaded the model, activated the physical owner, generated four
tokens cold, generated four tokens from an exact cached prefix, verified equal
output plus hit/miss telemetry, shut down with zero request/reservation owners,
and closed the backend.

- Result: PASS
- Total process elapsed time: 0.20 seconds
- Peak resident set: 125,476 KiB

These are host-local smoke measurements, not a comparative benchmark. Cold,
repeated-prefix, alternating-prefix, and eviction comparisons against snapshot
execution remain future optimization evidence and are not prerequisites for
keeping this activation default-off.
