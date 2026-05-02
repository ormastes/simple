# Zstd FSE encoder `nb_bits` formula conflates `state_offset` with bit-count selector

**Status:** OPEN. Identified 2026-05-02 by W12-E end-to-end trace.
**Severity:** blocks W9-C FSE encoder primitives from round-tripping. Pure-Simple FSE encoder produces invalid bit-streams.
**Path:** `bug` track, encoder algorithm rewrite.

## Symptom

W9-C landed FSE encoder primitives in `src/lib/common/compress/zstd_fse.spl`. Round-trip through the existing pure-Simple FSE decoder fails: the decoder's state walk diverges from what the encoder produced.

W12-E diagnostic concluded this is a SEPARATE bug from the HUF decoder strict-invariant issue (filed at `zstd_huf_decoder_strict_remaining_invariant_2026-05-02.md`).

## Root cause

`src/lib/common/compress/zstd_fse.spl:415` — the encoder's bit-count selector:

```spl
if state + entry.state_offset >= 0
   and ((state + entry.state_offset) >> table.table_log) > 0:
    nb_bits = entry.nb_bits - 1
```

This conflates **`state_offset`** (which carries `delta_find_state` semantics in the FSE algorithm — i.e., where in the symbol's contiguous slot range the next state lands) with the **bit-count selector** (`nb_bits` choice between `floor(log2(table_size / count))` and that + 1).

The actual FSE encoder algorithm requires per-symbol slot lists in the form `(state=p, bits, baseline)` where:
- `bits = table_log - highbit(next_state_counter)`
- `baseline = (next_state_counter << bits) - table_size`

mirroring the decoder's reverse-walk formulas. The current encoder formula does NOT implement this; it sloppily reuses `state_offset` as a bit-budget proxy.

## Affected encoder

- W9-C `_zstd_fse_encode_one_symbol` (`src/lib/common/compress/zstd_fse.spl:415`)
- Public encoder API `zstd_fse_encode_symbols` derived from it

## Fix scope

**Rewrite-grade**. The fix requires:

1. Restructuring the encoder's per-symbol table to a slot-list form `[(state, bits, baseline), ...]` per FSE specification.
2. Replacing the single-formula `nb_bits` selector with a state-walk-driven slot lookup.
3. Updating `_zstd_fse_encode_one_symbol` to:
   - Look up the symbol's slot list
   - Walk from current state to next state via `(next_state >> bits, next_state & ((1<<bits)-1))` decomposition
   - Emit `(next_state - baseline)` worth of bits

Reference: FSE algorithm spec (Yann Collet, 2014) and RFC 8478 §4.1.1.4 ("Encoding"); but the cleanest derivation is to take the existing pure-Simple **decoder** state-table (which is correct) and produce the encoder dual.

W12-E noted: "I had cycled through three mental models without converging" — the algorithm rewrite hits the 2-3-attempt discipline limit and was deferred per `feedback_no_coverups.md`.

## Verification

After fix:
- Round-trip a small input through `zstd_fse_encode_symbols` → `zstd_fse_decode_symbols` byte-exact.
- Cross-check against `zstd` CLI FSE-encoded literal weight headers.

## Out of scope

- The orthogonal HUF decoder strict-invariant bug (filed at `zstd_huf_decoder_strict_remaining_invariant_2026-05-02.md`).
- Façade level relax {3}→{1,2,3} — verified by W12-E to NOT route through this encoder.

## Cross-references

- `doc/08_tracking/bug/bug_zstd_huf_literal_encoder_bit_layout_2026-05-02.md` § revised hypothesis (W12-E investigation).
- W12-E commit `7a2d261b50c1`.
- `src/lib/common/compress/zstd_fse.spl:415` (broken formula).
- Existing pure-Simple FSE decoder `_zstd_fse_decode_one_symbol` (correct reference dual).
