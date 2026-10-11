# Spreadsheet ASC/JIS UTF-8 corruption

Requirement: REQ-SHEETS-ASCII-WIDTH-UTF8. Convert ASCII width while preserving all
other Unicode codepoints, including supplementary characters and embedded NUL.

The release implementation used `slice(i, i + 1)` and then decoded that byte as a
character. UTF-8 characters occupy multiple bytes; a one-byte fragment cannot
represent full-width ASCII, Japanese text, or emoji. Five retained failures in
`formula_locale_text_spec.spl` correspond to four ASC cases and JIS Japanese
pass-through. Unchanged conversion bodies extracted from release reproduce those
five failures plus three related Unicode failures: 10 executed, 2 passed, 8 failed.

ASC/JIS now share `app.office.sheets.ascii_width`. Its cursor advances over UTF-8
continuation bytes, slices one complete character, and decodes only index zero of
that character. `common.string_builder.RtStringBuilder` appends output and consumes
its handle at finish. Each input byte is examined a bounded number of times; output
does not repeatedly copy an accumulated prefix. Formula dispatch imports the owner
for ASC, JIS, and DBCS. No other caller referenced the removed private helpers.

The existing UTF-8 codec was considered, but importing its sequence-length helper
also imported SIMD providers and introduced seed engine/family warnings. The local
cursor needs no codec/provider import. `char_at` was rejected because it is
codepoint-indexed in the seed and byte-indexed in the pure Simple interpreter and
native runtime. Byte indexing, byte slices, decoding a complete character at index
zero, and the runtime builder are shared by those counterparts. No Rust or runtime
source was modified. Pure Simple execution qualification is pending; inspection is
not execution proof. The pre-existing formula tokenizer's separate `char_at` use is
outside this owner fix and must be checked separately in that lane.

## Phase 1 evidence, 2026-10-11

- Release base: `26589b27e60d613605f75d395cd0334870801015`.
- New captured Stage 1 diagnostic producer: SHA-256
  `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`,
  16,347,136 bytes. Before/copy/after hashes agree. This is not the retained
  `0f2b8375...` producer, and no retained qualification was relabeled.
- Isolated source projection: 129 original release files, 1,608,938 bytes, plus
  unchanged builder dependencies and the owned change. Shared dirty root preserved.
- `ascii_width_spec.spl`: final 10 executed, 10 passed, 0 failed/skipped/dropped.
- `ascii_width_long_spec.spl`: 4 executed, 4 passed, 0 failed/skipped/dropped.
- 24 cold/warm timing rows compare exact output and byte counts for ASC/JIS,
  ASCII and multibyte/emoji/NUL inputs. Warm time ratios for 4x larger input:
  ASC ASCII 3.51, JIS ASCII 4.03, ASC Unicode 4.08, JIS Unicode 4.15.
  Largest timing input is 26,624 bytes. These are one-host diagnostics, not an SLA.
- Separate 90,112-byte input / 106,496-byte output memory control: exact oracle
  passed; observed process peak working set 22,515,712 bytes over 39 samples,
  wall time 2.995 seconds. The earlier exited-process perf property was null;
  no RSS claim is based on it.
- **Full formula baseline BLOCKED:** original `formula_locale_text_spec.spl`
  stopped before execution in unchanged release
  `src/lib/nogc_sync_mut/io/windows_redirected_process.spl`:
  `Unexpected token: expected Fn, found Colon`. Exit 1, declared >=36,
  executed/passed/failed/skipped/dropped all zero. No assertion was weakened and
  this file is not marked green. The focused owner tests are the scope admitted
  here; there is no global bootstrap, Stage 2, release-runtime, or cross-host claim.

Local evidence: `build/sol-phase1-unicode-release-20261011/` holds the producer,
manifests, before/after logs, perf records, and memory control. The immutable
producer ran each focused spec directly with `SIMPLE_LIB=<projection>/src`, isolated
`SIMPLE_HOME`/`SIMPLE_CACHE_DIR`, and `SIMPLE_NO_STUB_FALLBACK=1`.
Bug database reconciliation remains pending because no qualified bug DB tool was
used in this Stage 1 diagnostic lane.
