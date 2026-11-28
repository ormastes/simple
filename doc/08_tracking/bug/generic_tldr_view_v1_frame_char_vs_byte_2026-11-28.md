# generic_tldr_view_v1: v1 frame writer counts characters, reader reads bytes

- **Date:** 2026-11-28
- **Found by:** Fable review of the S3-F0 restore (byte framing everywhere).
- **Where:** `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl` `_frame_v1` (line ~152, writes `value.len()`, characters) versus `_read_frame_v1` (line ~408, reads that many bytes).
- **Symptom:** a v1 generic template section holding a non-ASCII name does not round-trip: the decoder reads too few bytes and fails or misframes. ASCII sections are unaffected.
- **Expected:** one unit. The model (`src/compiler/30.types/generic_subst/`) and the template projector now frame in bytes; `_frame_v2` already does. `_frame_v1` and its digests should move to `byte_len()` (a persisted v1 digest changes for non-ASCII names only) or be deduplicated onto the model in F2/F5.
- **Status:** open, not fixed in the F0 lane.
