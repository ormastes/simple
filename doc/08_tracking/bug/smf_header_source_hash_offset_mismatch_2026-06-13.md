# BUG: SMF header `source_hash` write/read offset mismatch (68 vs 84)

## Closed 2026-09-13 — Fixed: writer and validator now agree on offset 68

- **measured** (grep of current source): `src/compiler/70.backend/linker/smf_header.spl:514` reads `source_hash: bytes_to_u64_le_header(bytes, offset + 68)`, matching the `to_bytes()` write order at `:411`.
- **measured**: `src/compiler/80.driver/cache/cache_validator.spl:293` now reads `self.u64_at(start + 68)` in `fn source_hash()`. The 84 offset the bug reported is gone from that reader; the only remaining `84` in `smf_header.spl` is `reserved_hints` at `:520`, a different field.
- **inferred**: with both sides on 68 the 16-byte discrepancy cannot produce a false cache hit or miss. Not runtime-exercised here — no self-hosted binary is deployed and the seed does not take the pure-Simple SMF validator path.

- **ID:** `smf_header_source_hash_offset_mismatch`
- **Severity:** P2 (latent — user-script SMF cache validator may read the wrong bytes)
- **Found:** 2026-06-13, perf-umbrella Lane B (AC-7 dynSMF cache work, while confirming the
  existing `simple run` content-hash path — out of AC-7 scope, recorded not fixed).

## Symptom
- `src/.../smf_header.spl` `to_bytes()` writes `source_hash` at header offset **68**.
- `src/compiler/.../cache_validator.spl` (`validate_smf_with_deps`, ~line 103) reads the
  embedded source-hash field at `header_start + 84`.
A 16-byte discrepancy. If both paths are exercised, the validator compares the wrong bytes,
which could make the unchanged-script cache either falsely hit or falsely miss.

## Why it may be masked today
The user-script cache also hashes the source via `rt_hash_text` and may short-circuit before
the offset-84 read matters, so the latent mismatch has not produced an obvious failure.

## Impact
- Risk to AC-7's "unchanged-script cache reuse" correctness for the `simple run` lane (the
  lane AC-7 deliberately did NOT modify). The new dynSMF lane uses a `.srchash` sidecar and
  is unaffected.

## Proposed next step
Pick one canonical offset for `source_hash`; make `to_bytes()` writer and `cache_validator`
reader agree; add a round-trip spec (`write header → read field → equal`).

## Status
CLOSED 2026-09-13 (fixed; both sides read offset 68). Originally: OPEN — recorded. Out of AC-7 scope (sidecar lane unaffected). Validate before relying on the
user-script SMF source-hash field.
