# scv pack-import: "pack object hash mismatch" diagnostic is unreachable (masked by verify)

Date: 2026-08-27
Status: FIXED 2026-08-27 — `scv_pack_payload_matches_manifest_bytes` now returns
        `(bool, i64, text)`; the third element carries the object-level reason and
        both call sites emit it before the generic pack-level message.
        `test/integration/app/scv_pack_import_spec.spl` 5/7 -> 7/7.
Class: (b) real product bug — unreachable defensive branch + coarse diagnostic
Found by: root-causing long-standing RED `test/integration/app/scv_pack_import_spec.spl` (3/7)

## Symptom
The example "rejects pack metadata objects whose payload does not match the
object id" asserts `pack-import` emits

    ERROR pack object hash mismatch: file_

The corruption IS rejected (`bad_code=1`), but the message is

    ERROR pack manifest payload mismatch: pack_b60bae5d...

## Root cause
The same content-vs-id hash check exists at two layers, and the outer one always
wins.

- Outer: `scv_pack_import_from_dir` (`src/lib/scv/pack.spl:357`) calls
  `scv_pack_verify_dir` at line 360 and returns its error verbatim before any
  import work happens.
- `scv_pack_verify_dir` -> `scv_pack_payload_matches_manifest_bytes`
  (`pack.spl:149`) already calls `scv_pack_payload_object_hash_ok` at line 186.
  That helper returns a plain `bool`, so a hash failure is flattened into
  `payload_ok = false` and reported as the generic
  `ERROR pack manifest payload mismatch: {pack_id}` (`pack.spl:229/231`).
- Inner: `scv_pack_import_entry` (`pack.spl:292`) has six distinct
  `ERROR pack object hash mismatch: {id}` branches (kinds `files`, `trees`,
  `commits`, `conflicts`, `syntax`) plus `ERROR chunk content mismatch`. Because
  verify has already rejected exactly the same corruption over exactly the same
  objects, **none of these branches can be reached through `pack-import`.**

## Second instance of the same masking (same root cause)
The example "rejects pack payload entries with unsafe object ids even when
manifest and payload agree" is masked identically. After its fixture was
repaired (it previously failed the outer pack-id check and never reached the
payload at all), the corruption is still rejected — but as
`ERROR pack manifest payload mismatch: pack_ee971daf...`, not the expected
`ERROR unsafe pack object id: bad_id`. The cause is the same flattening:
`scv_pack_payload_matches_manifest_bytes` validates the id prefix at
`pack.spl:169` (`scv_pack_id_prefix_valid`) and returns a bare `false`, so the
specific message from `scv_pack_import_entry` (`pack.spl:299`) is unreachable.
Both branches (`ERROR unsafe pack object id` and `ERROR pack object hash
mismatch`) are dead for the same reason and are fixed by the same change.

## Impact
Correctness of the rejection is fine — corrupt packs are refused either way.
The cost is diagnostic quality and dead code: an operator sees a pack-level
message naming the pack id, with no indication of which object is corrupt or of
what kind, while the code that would have said precisely that is unreachable.

## Suggested fix (not applied here)
Have `scv_pack_payload_matches_manifest_bytes` return the offending
`(kind, id)` instead of a bare bool, and let `scv_pack_verify_dir` emit
`ERROR pack object hash mismatch: {id}` for that case. That makes the specific
message reachable from both entry points and removes the duplication, but it
changes an error string that other callers/specs may match on, so it wants its
own reviewed change rather than being folded into a triage pass.

## Spec status
`scv_pack_import_spec.spl`'s assertion is NOT stale — it pins the diagnostic the
code was clearly written to produce. It is left RED deliberately; weakening it to
match the coarser message would hide the unreachable-branch defect.

## Fix as applied (2026-08-27)
`src/lib/scv/pack.spl`
- `scv_pack_payload_matches_manifest_bytes` signature `-> (bool, i64)` becomes
  `-> (bool, i64, text)`. All generic rejections return `""` as the reason;
  the id-prefix rejection returns `ERROR unsafe pack object id: {parts[2]}`
  and the content-hash rejection returns
  `ERROR pack object hash mismatch: {parts[2]}` — the exact strings the
  previously dead branches in `scv_pack_import_entry` emit.
- `scv_pack_verify_dir` checks `payload_reason` **before** the entry-count
  comparison. Order is load-bearing: a rejected object also short-counts
  entries, so checking the count first flattens every specific reason away —
  that ordering was the masking.

`src/lib/scv/pack_v2.spl`
- The v1 fallback branch (the only other caller) destructures the 3-tuple and
  propagates a non-empty reason the same way.

No spec was weakened: the two examples still assert the specific object-level
diagnostics they always asserted, and they now reach real code. The generic
`ERROR pack manifest payload mismatch: {pack_id}` is unchanged for every
failure that genuinely has no object-level cause.
