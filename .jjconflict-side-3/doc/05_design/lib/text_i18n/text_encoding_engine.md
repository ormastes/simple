# Text Encoding Engine — Architecture Design

**Feature:** text-encoding-engine
**Phase:** 3-arch
**Date:** 2026-04-27
**Author:** SStack Architect (Claude Sonnet)

---

## 1. Storage Location Decision (D-1)

**Decision: EXTEND existing `encoding/` and `unicode/` namespaces; ADD new `text/` namespace for new types; ADD mutable builders in `nogc_sync_mut/text/`.**

Rationale:
- `src/lib/common/encoding/utf8.spl`, `text_ops.spl`, `unicode_text.spl` and `src/lib/common/unicode/codepoint.spl` already have downstream callers throughout the compiler and stdlib. Renaming or moving them would require a migration sweep with no functional gain.
- New value types (`Text`, `TextView`) and their supporting structures (`Checkpoint`) have no existing callers — they belong in a fresh `src/lib/common/text/` namespace per the Phase 1 locked default (state.md decision #2).
- New encoding converters (CP949, Shift_JIS, GB18030, Big5) are logically part of the encoding family — they go in `src/lib/common/encoding/` next to `utf8.spl`, not in `text/`.
- Mutable `TextBuilder` carries allocator dependency → `src/lib/nogc_sync_mut/text/text_builder.spl`.

No caller migration in this change. `String::to_text()` and `Text::to_string()` adapters bridge old and new APIs. Mass migration is a separate follow-up ticket.

---

## 2. Fixed-Width Strategy Decision (D-2)

**Decision: Hybrid SmallString (23B SSO) + Sparse Checkpoint K=64 — confirmed from Phase 2 lean.**

Rationale vs. the other 3 candidates (from `api_and_design.md`):

| Candidate | Verdict | Reason rejected / confirmed |
|---|---|---|
| A: UTF-32 shadow buffer | Rejected | 4× memory; Korean/CJK strings (3B/cp) widen to 4B/cp; unacceptable for v1 |
| B: Sparse checkpoint only | Rejected (standalone) | No SSO; compiler short-string profile (identifiers ≤23B) gets heap allocation |
| C: PEP-393 tagged repr | Rejected | Widening penalty for Hangul/CJK; requires 3 separate code paths; complexity not justified |
| D: Hybrid SmallString + Sparse Checkpoint | **Confirmed** | SSO for ≤23B (compiler hot path, zero alloc); checkpoint for long strings; always-UTF-8 wire format |

K=64 is compile-time fixed for v1. Variable-K is an open question for Phase 4 (see §8).

SSO layout is expressed as a tagged union via composition — NOT inheritance:

```
# TextStorage composition (no class X(Y) inheritance)
class TextInline:
    bytes: [u8; 23]
    len: u8              # 0..23; high bit unused (reserved for tag)

class TextHeap:
    ptr: *u8
    len: u32
    cap: u32
    cp_len: u32          # cached codepoint count; u32::MAX = dirty
    checkpoint: ?CheckpointTable

class Text:
    # Tagged union via composition — one of inline or heap is active
    # tag: bit 0 of storage_tag field
    storage_tag: u8
    inline: TextInline
    # heap overlaps inline storage on 64-bit; see note below
```

Note: exact tagged-union layout is for Phase 5 (implementer) to finalize based on Simple's struct-layout rules. The arch constraint is: no inheritance, tag-discriminated composition.

---

## 3. Module List

### 3.1 MODIFIED files (extend existing)

| File | Role | Changes |
|---|---|---|
| `src/lib/common/encoding/utf8.spl` | UTF-8 codec foundation | Add `utf8_validate_dfa()` scalar DFA, `utf8_replace_invalid()`, SIMD FFI hook `utf8_validate_fast()` that dispatches to Rust FFI in compiled mode |
| `src/lib/common/encoding/text_ops.spl` | CharMode abstraction | Add `text_grapheme_len_mode()`, `text_grapheme_at_mode()` for grapheme cluster support |
| `src/lib/common/encoding/unicode_text.spl` | Unicode-aware ops | Add `utext_normalize_nfc()`, `utext_grapheme_iter()`, `utext_display_width()` correction for emoji/CJK |
| `src/lib/common/unicode/codepoint.spl` | Codepoint properties | Add `is_hangul_syllable()`, `is_hangul_jamo()`, `is_emoji_modifier_base()`, `is_regional_indicator()`, `grapheme_break_property()` |

### 3.2 NEW files — encoding converters (`src/lib/common/encoding/`)

| File | Role | Notes |
|---|---|---|
| `src/lib/common/encoding/cp949.spl` | CP949/EUC-KR ↔ UTF-8 | WHATWG state machine; CP949 supersedes EUC-KR per WHATWG normative spec; lead bytes 0x81–0xFE |
| `src/lib/common/encoding/shift_jis.spl` | Shift_JIS ↔ UTF-8 | WHATWG decoder state machine; handles Windows-31J extension |
| `src/lib/common/encoding/gb18030.spl` | GB18030 ↔ UTF-8 | 207 range-pairs (arithmetic, no full table); covers full Unicode |
| `src/lib/common/encoding/big5.spl` | Big5 ↔ UTF-8 | WHATWG Big5 decoder; handles HKSCS extension flag |
| `src/lib/common/encoding/utf16.spl` | UTF-16 LE/BE/BOM ↔ UTF-8 | Surrogate pair handling; BOM detection; v1 converts to/from UTF-8 |
| `src/lib/common/encoding/utf32.spl` | UTF-32 LE/BE ↔ UTF-8 | Straight 4-byte ↔ UTF-8; BOM detection |
| `src/lib/common/encoding/iso8859_1.spl` | ISO-8859-1 + Windows-1252 ↔ UTF-8 | Table-free (ISO-8859-1 = Unicode codepoints 0–255); Win-1252 uses small 32-entry patch table |
| `src/lib/common/encoding/encoding_trait.spl` | `trait Encoding` definition | Shared trait + `EncErr` error type; all converters implement this |

### 3.3 NEW files — Unicode tables (`src/lib/common/unicode/`)

| File | Role | Notes |
|---|---|---|
| `src/lib/common/unicode/hangul.spl` | Hangul NFC/NFD arithmetic | Pure arithmetic §3.12 — SBase=0xAC00, LCount=19, VCount=21, TCount=28; ZERO codegen dependency |
| `src/lib/common/unicode/normalize.spl` | NFC normalization (general) | Depends on UCD-codegen tables; imports `hangul.spl` for Hangul fast-path |
| `src/lib/common/unicode/grapheme.spl` | UAX #29 grapheme cluster iteration | Subset for v1: extended grapheme clusters; emoji ZWJ sequences; Hangul syllable clusters |
| `src/lib/common/unicode/ucd_nfc_tables.spl` | UCD-generated NFC composition tables | AUTO-GENERATED by `scripts/codegen/ucd_tables.shs`; do not edit manually |
| `src/lib/common/unicode/ucd_grapheme_tables.spl` | UCD-generated grapheme break tables | AUTO-GENERATED; updated per Unicode version |

### 3.4 NEW files — Text value types (`src/lib/common/text/`)

| File | Role | Notes |
|---|---|---|
| `src/lib/common/text/checkpoint.spl` | Sparse codepoint→byte index table | `class CheckpointTable`; K=64 compile-time constant; build/invalidate/lookup ops |
| `src/lib/common/text/text.spl` | `Text` value type | Hybrid SSO+heap; public read API: `len_bytes`, `len_codepoints`, `len_graphemes`, `cp_at`, `byte_at`, `slice_bytes`, `slice_codepoints`, `contains`, `find`, `to_upper`, `to_lower`, `normalize_nfc` |
| `src/lib/common/text/text_view.spl` | `TextView` non-owning slice | Borrows byte range from a `Text`; same read API as `Text` without allocation |
| `src/lib/common/text/iter.spl` | Iterator types | `ByteIter`, `CodepointIter`, `GraphemeIter`; all implement `trait Iterator<T>` |
| `src/lib/common/text/adapters.spl` | Bridge to existing `String`/`str` | `fn text_from_string(s: str) -> Text`, `fn text_to_string(t: &Text) -> String`; minimal glue, no migration |

### 3.5 NEW files — Mutable builder (`src/lib/nogc_sync_mut/text/`)

| File | Role | Notes |
|---|---|---|
| `src/lib/nogc_sync_mut/text/text_builder.spl` | `TextBuilder` mutable accumulator | Append/insert/delete/replace; checkpoints invalidated on mutation; `fn build() -> Text` finalizes |

### 3.6 NEW files — Codegen script and Rust FFI

| File | Role | Notes |
|---|---|---|
| `scripts/codegen/ucd_tables.shs` | UCD parser → `.spl` const tables | Reads: `UnicodeData.txt`, `DerivedNormalizationProps.txt`, `GraphemeBreakProperty.txt`, `HangulSyllableType.txt`; emits `ucd_nfc_tables.spl` + `ucd_grapheme_tables.spl` |
| `src/runtime/src/text_simd.rs` | Rust SIMD FFI | Exports `rt_utf8_validate_simd(ptr: *const u8, len: usize) -> bool`; uses simdutf or inline Rust SIMD; runtime dispatch via CPUID |

### 3.7 NEW files — Tests

| File | Role | Notes |
|---|---|---|
| `test/lib/text/corpus_12lang_spec.spl` | 12-language Phase 4 corpus spec | Korean, CJK, Arabic, Devanagari, Hebrew, Thai, Vietnamese, Greek, Cyrillic, Emoji ZWJ; validates length/index/NFC/roundtrip per language |

**Summary: 7 MODIFIED, 21 NEW (15 `.spl`, 1 `.shs`, 1 `.rs`, 4 auto-generated `.spl`, 1 test `.spl`)**

---

## 4. Core Interfaces

### 4.1 Encoding trait (in `encoding_trait.spl`)

```
class EncErr:
    message: str
    byte_offset: i64

trait Encoding:
    fn decode(bytes: [u8]) -> Result<Text, EncErr>
    fn encode(t: &Text) -> [u8]
    fn decode_lossy(bytes: [u8]) -> Text     # replaces invalid sequences with U+FFFD
    fn name() -> str                         # IANA/WHATWG label, e.g. "EUC-KR"
```

### 4.2 Text value type (in `text.spl`)

```
class Text:
    # Internal: tagged SSO/heap storage (composition, no inheritance)
    # Public API only — layout is implementation detail:

    fn len_bytes(self) -> i64
    fn len_codepoints(self) -> i64
    fn len_graphemes(self) -> i64

    fn byte_at(self, i: i64) -> u8
    fn cp_at(self, i: i64) -> i64              # returns Unicode codepoint as i64
    fn grapheme_at(self, i: i64) -> TextView   # grapheme cluster as slice

    fn slice_bytes(self, start: i64, end: i64) -> TextView
    fn slice_codepoints(self, start: i64, end: i64) -> TextView
    fn slice_graphemes(self, start: i64, end: i64) -> TextView

    fn contains(self, needle: &Text) -> bool
    fn find(self, needle: &Text) -> ?i64       # byte offset of first match, or None

    fn to_upper(self) -> Text
    fn to_lower(self) -> Text
    fn normalize_nfc(self) -> Text

    fn bytes(self) -> ByteIter
    fn codepoints(self) -> CodepointIter
    fn graphemes(self) -> GraphemeIter

    fn to_string(self) -> String               # bridge to existing String type
    fn is_ascii(self) -> bool
    fn is_empty(self) -> bool
```

### 4.3 TextView (in `text_view.spl`)

```
class TextView:
    # Non-owning slice; borrows byte range from a Text
    fn len_bytes(self) -> i64
    fn len_codepoints(self) -> i64
    fn to_text(self) -> Text               # copies into owned Text
    fn as_bytes(self) -> &[u8]
    fn contains(self, needle: &Text) -> bool
    fn find(self, needle: &Text) -> ?i64
```

### 4.4 TextBuilder (in `text_builder.spl`)

```
class TextBuilder:
    fn new() -> TextBuilder
    fn append(self, t: &Text)
    fn append_str(self, s: str)
    fn append_codepoint(self, cp: i64)
    fn insert_codepoints(self, at: i64, t: &Text)
    fn delete_codepoints(self, start: i64, end: i64)
    fn replace_codepoints(self, start: i64, end: i64, t: &Text)
    fn build(self) -> Text                 # invalidates builder; checkpoints built lazily
```

### 4.5 Normalizer trait (in `normalize.spl`)

```
trait Normalizer:
    fn normalize_nfc(t: &Text) -> Text
    fn normalize_nfd(t: &Text) -> Text     # v1: Hangul only; general NFD is follow-up

class HangulNormalizer:
    # implements Normalizer via §3.12 arithmetic
    # impl Normalizer for HangulNormalizer

class UcdNormalizer:
    # implements Normalizer via UCD-generated tables
    # impl Normalizer for UcdNormalizer
```

### 4.6 Iterator types (in `iter.spl`)

```
class ByteIter:
    fn next(self) -> ?u8

class CodepointIter:
    fn next(self) -> ?i64

class GraphemeIter:
    fn next(self) -> ?TextView
```

### 4.7 CheckpointTable (in `checkpoint.spl`)

```
const CHECKPOINT_STRIDE: i64 = 64

class CheckpointEntry:
    byte_offset: u32
    cp_count: u32

class CheckpointTable:
    entries: [CheckpointEntry]
    fn build(bytes: &[u8]) -> CheckpointTable
    fn cp_count_to_byte_offset(self, cp_idx: i64, bytes: &[u8]) -> i64
    fn byte_offset_to_cp_count(self, byte_off: i64, bytes: &[u8]) -> i64
    fn invalidate(self)
    fn is_valid(self) -> bool
```

---

## 5. Data Flow

### 5.1 Decode path (external bytes → Text)

```
raw bytes (any encoding)
  → Encoding::decode(bytes) → validates + converts to UTF-8 byte vector
  → Text::from_utf8_unchecked(vec)  [only called from within Encoding impls after validation]
  → Text { storage: SSO if len≤23, else Heap { ptr, len, cap, cp_len=dirty, checkpoint=None } }
```

SIMD fast-path for UTF-8 input:
- `len < 16`: scalar DFA (`utf8_validate_dfa`)
- `len >= 16` in compiled mode: `rt_utf8_validate_simd(ptr, len)` via Rust FFI
- `len >= 16` in interpreter mode: scalar DFA
- Threshold for FFI crossover (exact bytes) deferred to Phase 4 microbench

### 5.2 Random codepoint access path

```
text.cp_at(i)
  ├── SSO branch (len≤23): linear scan from byte 0, O(23) bounded
  └── Heap branch:
      ├── checkpoint == None or dirty → CheckpointTable::build(bytes) → O(n) one pass
      └── checkpoint valid → CheckpointTable::cp_count_to_byte_offset(i, bytes) → O(K=64)
          → utf8_decode_one(bytes, byte_offset) → codepoint
```

### 5.3 Mutation path (TextBuilder)

```
TextBuilder::delete_codepoints(start, end)
  → locate byte range via checkpoint (O(K)) or scan (SSO)
  → shift bytes in heap buffer → O(n)
  → checkpoint.invalidate() → cp_len = dirty
  → next cp_at() call triggers lazy CheckpointTable::build()
```

### 5.4 NFC normalization path

```
text.normalize_nfc()
  → CodepointIter over Text bytes
  → for each codepoint:
      is_hangul_syllable(cp) → HangulNormalizer::compose(L, V, T) — zero tables, O(1) per syllable
      else → UcdNormalizer::compose(cp, context) — UCD table lookup
  → TextBuilder::append_codepoint() for each normalized cp
  → TextBuilder::build() → new Text
```

### 5.5 Encoding convert path (Text → external bytes)

```
text.encode_to(encoding: &impl Encoding)
  → Encoding::encode(&text)
  → iterates CodepointIter over text.bytes
  → converts each codepoint to target encoding bytes
  → returns [u8] (caller owns)
```

---

## 6. Integration with Existing `String`/`str`

New types coexist with current `String`/`str`. No existing callers are broken in this change.

Adapter functions in `text/adapters.spl`:

```
fn text_from_str(s: str) -> Text
    # Wraps existing str bytes as Text; O(n) for validation (already-valid UTF-8 fast-path)

fn text_to_string(t: &Text) -> String
    # Copies Text bytes into a new String allocation

fn string_to_text(s: &String) -> Text
    # Same as text_from_str but from String
```

Callers of existing `utext_*`, `text_*_mode` functions are unaffected. Those functions remain in place. The Text type is additive.

---

## 7. Codegen Plan

`scripts/codegen/ucd_tables.shs` (Shell script — the 3 allowed bootstrap scripts are `.sh`/`.shs`):

- **Inputs**: UCD files from `data/ucd/` (downloaded by build system or checked in):
  - `UnicodeData.txt` — canonical decomposition mappings
  - `DerivedNormalizationProps.txt` — composition exclusions, full composition pairs
  - `GraphemeBreakProperty.txt` — UAX #29 grapheme break property per codepoint range
  - `HangulSyllableType.txt` — L/V/T/LV/LVT classification (cross-check for arithmetic)
- **Outputs**:
  - `src/lib/common/unicode/ucd_nfc_tables.spl` — NFC composition table as const array
  - `src/lib/common/unicode/ucd_grapheme_tables.spl` — grapheme break table as range-pair const array
- **When to run**: build time, AFTER a working Simple compiler exists (not bootstrap-time). The generated files are checked into source control so a cold build works without running codegen.
- **Bootstrap dependency note**: `hangul.spl` has ZERO codegen dependency — Hangul NFC works at any phase. General NFC (`normalize.spl`) requires the generated tables. If codegen slips, disable `UcdNormalizer` and leave `HangulNormalizer` active.
- **Unicode version**: generated files MUST include a header comment stating the Unicode version (e.g., `# Unicode 15.1.0`). Any update requires re-running codegen and a separate commit.

---

## 8. Open Architectural Questions (for Phase 4/5)

| ID | Question | Impact |
|---|---|---|
| OQ-1 | SIMD dispatch threshold: at what `len_bytes` does Rust FFI overhead beat scalar DFA? Phase 2 estimates 450 MB/s scalar vs 12 GB/s SIMD; FFI call cost ~50–200ns; crossover likely 64–512 bytes. Needs Phase 4 microbench. | SIMD path in `utf8.spl` |
| OQ-2 | Variable-K checkpoints: should K be tunable per string based on length percentiles (K=32 for >4KB strings)? Phase 2 recommends fixed K=64; variable-K adds ~20% implementation complexity. | `checkpoint.spl` |
| OQ-3 | TextBuilder ownership model: does `build()` consume the builder or allow reuse? Consuming builder (moves out) is safer; reuse requires explicit `reset()`. | `text_builder.spl` API |
| OQ-4 | `?i64` (Option type) syntax: confirm `?T` is the correct optional syntax in current Simple grammar before Phase 5. | All public APIs |
| OQ-5 | Encoding table binary size budget: CP949+Shift_JIS+GB18030+Big5 ≈350 KB compiled-in `.rodata`. Acceptable for server; may require feature flag for embedded targets. Phase 5 to decide. | `encoding/` converters |
| OQ-6 | Thread-safety: `Text` is value-type immutable (safe); `TextBuilder` is single-owner mutable (safe). Lazy checkpoint rebuild is single-threaded (safe for value types). Confirm no shared mutable checkpoint state escapes through `TextView`. | `text.spl`, `text_view.spl` |
| OQ-7 | NFD / NFKC / NFKD normalization: deferred to v2. Record as follow-up ticket. Same for full UAX #29 word/line/sentence iteration and BiDi (UAX #9). | `normalize.spl` |

---

## 9. Dependency Map

```
# Layer 0 — no deps
encoding/utf8.spl
unicode/codepoint.spl
unicode/hangul.spl                  # pure arithmetic, zero table dep

# Layer 1 — depends on Layer 0
encoding/text_ops.spl               -> encoding/utf8.spl
encoding/encoding_trait.spl         -> text/text.spl (forward ref; text.spl also refs this)
unicode/ucd_nfc_tables.spl          -> (codegen output, no runtime dep)
unicode/ucd_grapheme_tables.spl     -> (codegen output, no runtime dep)
text/checkpoint.spl                 -> encoding/utf8.spl

# Layer 2 — depends on Layer 0+1
encoding/unicode_text.spl           -> encoding/utf8.spl, encoding/text_ops.spl, unicode/codepoint.spl
unicode/grapheme.spl                -> unicode/codepoint.spl, unicode/ucd_grapheme_tables.spl
unicode/normalize.spl               -> unicode/hangul.spl, unicode/ucd_nfc_tables.spl, unicode/codepoint.spl
text/iter.spl                       -> encoding/utf8.spl, unicode/grapheme.spl, text/checkpoint.spl
text/text_view.spl                  -> encoding/utf8.spl, text/checkpoint.spl

# Layer 3 — depends on Layer 0+1+2
text/text.spl                       -> text/checkpoint.spl, text/iter.spl, text/text_view.spl,
                                       unicode/normalize.spl, encoding/unicode_text.spl
encoding/cp949.spl                  -> encoding/encoding_trait.spl, text/text.spl
encoding/shift_jis.spl              -> encoding/encoding_trait.spl, text/text.spl
encoding/gb18030.spl                -> encoding/encoding_trait.spl, text/text.spl
encoding/big5.spl                   -> encoding/encoding_trait.spl, text/text.spl
encoding/utf16.spl                  -> encoding/encoding_trait.spl, text/text.spl
encoding/utf32.spl                  -> encoding/encoding_trait.spl, text/text.spl
encoding/iso8859_1.spl              -> encoding/encoding_trait.spl, text/text.spl

# Layer 4 — top-level / mutable
text/adapters.spl                   -> text/text.spl (+ existing String type)
nogc_sync_mut/text/text_builder.spl -> text/text.spl, text/checkpoint.spl, encoding/utf8.spl

# Runtime (Rust)
src/runtime/src/text_simd.rs        -> (no Simple deps; called via rt_utf8_validate_simd extern)

# No circular dependencies: verified by layer ordering above.
```

---

## 10. Requirement Coverage (AC → Module)

| AC | Module(s) |
|---|---|
| AC-1 (encoding catalog) | `encoding/cp949.spl`, `encoding/shift_jis.spl`, `encoding/gb18030.spl`, `encoding/big5.spl`, `encoding/utf16.spl`, `encoding/utf32.spl`, `encoding/iso8859_1.spl`, `encoding/utf8.spl` (modified) |
| AC-2 (language matrix + Korean) | `unicode/hangul.spl`, `unicode/normalize.spl`, `unicode/grapheme.spl`, `unicode/codepoint.spl` (modified) |
| AC-3 (implementation survey) | Phase 2 research only; influences design decisions |
| AC-4 (fixed-width strategy) | `text/text.spl` (SSO+checkpoint), `text/checkpoint.spl` |
| AC-5 (text API spec) | `text/text.spl`, `text/text_view.spl`, `text/iter.spl`, `nogc_sync_mut/text/text_builder.spl` |
| AC-6 (repo inventory) | `text/adapters.spl` (bridge), all MODIFIED files |
| AC-7 (impl + SIMD + corpus) | `src/runtime/src/text_simd.rs`, `encoding/utf8.spl` (modified), `test/lib/text/corpus_12lang_spec.spl` |
| AC-8 (no regressions) | `text/adapters.spl`, all MODIFIED files keep existing public API |

---

## 11. Codex Dispatch Status

Codex `$design` was dispatched via `codex exec` to review the architecture. Results will be merged into this document once available. See `doc/05_design/text_encoding_engine_codex.md` for Codex output (written by Codex directly) or the codex dispatch status in `state.md §3-arch`.
