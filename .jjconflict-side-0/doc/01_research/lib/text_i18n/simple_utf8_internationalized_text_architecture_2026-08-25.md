<!-- codex-research -->

# Simple UTF-8 and Internationalized Text Architecture

**Research, repository audit, design, migration plan, and performance gates**

| Field | Value |
|---|---|
| Project | [`ormastes/simple`](https://github.com/ormastes/simple) |
| Repository snapshot | `main` at `112ac2030f0c5c442c480cb0e86916402e5c5eeb` |
| Research date | 2026-08-25 |
| Status | Proposed architecture and implementation plan |
| Canonical internal encoding | Validated UTF-8 |
| Unicode baseline | Unicode 17.0.0 |
| Locale-data baseline | CLDR 48.2.1; LDML 48.2 specification |
| Primary goals | Full international text correctness, low ASCII-path overhead, efficient transcoding and parsing, explicit indexing semantics, bounded memory growth, low allocation/RSS overhead, deterministic no-allocation profiles |

> **Terminology note:** This report uses **i18n** for internationalization and **l10n** for localization. “Character” is avoided where it is ambiguous: the report names bytes, Unicode scalar values, grapheme clusters, and display cells explicitly.

---

## 1. Executive decision

Simple should retain one canonical, immutable, contiguous, validated UTF-8 primitive: `text`. It should not replace that representation with UTF-16, UTF-32, Python-style variable-width storage, or a second unrelated `Text` object. Arbitrary bytes remain `[u8]` or a byte-buffer type. Every conversion from external bytes into `text` must validate or explicitly request replacement.

The architecture should be changed in four coordinated layers:

1. **Correctness layer.** Eliminate APIs that can create invalid UTF-8 `text`, remove ambiguous byte-versus-character operations, make encoding errors typed, and make parser spans consistently byte-based.
2. **Unicode and i18n layer.** Add explicit scalar, grapheme, normalization, locale, message-catalog, plural/select, identifier, and security semantics without placing locale logic in the general string hot path.
3. **Performance layer.** Add ASCII fast paths, streaming direct-to-UTF-8 decoders, block-oriented lexer scanning, optional sparse text indexes, builders, and complete SIMD kernels while preserving scalar reference implementations.
4. **Migration layer.** Preserve the current `text` ABI and byte-length behavior during the initial migration; add explicit APIs immediately and progressively lint ambiguous old APIs. Do not silently redefine `len()` or integer indexing in place.

### 1.1 Recommended type family

| Type | Invariant | Primary role | Allocation profile |
|---|---|---|---|
| `text` | Immutable, contiguous, valid UTF-8 | General strings, source text, paths where UTF-8 is required | Existing runtime allocation/interning |
| `TextSlice` | Borrowed UTF-8-boundary-aligned range | Zero-copy substring/view | None |
| `TextIndex` | Valid UTF-8 boundary represented by native byte offset | Efficient forward/backward movement | None |
| `TextCursor` | Owner-bound sequential traversal state | Parsing and iteration | None |
| `TextBuilder` | Mutable UTF-8 construction buffer | Formatting, decoding, joining | Amortized or fixed-capacity |
| `IndexedText` | `text` plus a lazy sparse scalar index | Repeated ordinal scalar access | Optional sidecar |
| `GraphemeView` | UAX #29 boundary view over text | UI editing and cursor movement | Lazy/optional |
| `Utf8Buf<N>` | Valid UTF-8 with byte capacity `N` and dynamic used length | Embedded/no-allocation text | Inline fixed storage |
| `Ascii<N>` | ASCII-only, byte capacity `N` | Protocol keys, message IDs, tiny hot paths | Inline fixed storage |
| `Bytes<N>` / `[u8]` | Arbitrary bytes | Binary I/O and undecoded input | Inline or existing array |
| `RopeText` | Balanced chunked UTF-8 text | Very large mutable documents | Chunked; editor profile only |
| `MessageId` / `Message` | Typed localization identity and schema | i18n, not general string storage | Compile-time/catalog driven |

### 1.2 Core compatibility choices

- Keep `text` stored as UTF-8 and preserve the current runtime header in the first implementation wave.
- Keep existing `text.len()` byte-oriented during the compatibility period. Add `byte_len()` and `scalar_len()` and lint ambiguous uses in Unicode-sensitive code.
- Treat integer `text[i]` as a legacy byte operation. `str_char_at()` now delegates to the runtime scalar accessor so safe code cannot manufacture a malformed one-byte `text`; add an explicitly named byte accessor for byte-oriented callers.
- Make byte slicing return `TextSlice`/`Result<text, BoundaryError>` only when both endpoints are UTF-8 boundaries.
- Use iterators/cursors for ordinary traversal. Use `IndexedText` only when a workload demonstrates repeated ordinal random access.
- Keep compiler/source spans as byte offsets. Convert to scalar, UTF-16, grapheme, or display columns lazily at the diagnostic/LSP/UI boundary.
- Decode legacy encodings only at I/O boundaries. Internal algorithms never carry an implicit “current encoding.”
- Keep i18n optional: builds without localization must not pay registry, hash-map, Unicode-data, or locale-selection overhead in their hot path.

### 1.3 Most important current defects to fix first

1. **Fixed in the working implementation:** `str_char_at()` now returns a complete scalar through `text.char_at()`. The retained ASCII comparison measured p50/p95 of 29,568/30,760 us versus 28,785/29,436 us for the unsafe byte-slice reference over 21 × 4,096 accesses. The correctness-required p95 cost is about 4.5%; an intrinsic fast path remains benchmark-gated.
2. unchecked byte-to-text construction permits malformed `text` values and breaks the canonical invariant.
3. the generic codec path materializes an intermediate array of integer code points and contains byte-by-byte UTF-8 reconstruction behavior that is incorrect for multibyte scalars.
4. “UTF-8 mode” and “full Unicode mode” are selected through mutable global state instead of explicit APIs/types.
5. the current width/rank-select implementation stores every scalar start in a global handle registry; it is neither sparse nor succinct and has avoidable locking/lifetime cost.
6. the Rust lexer scans and copies scalar by scalar even for ASCII-heavy source and duplicates work in i18n/f-string scanning.
7. two independent i18n extractors exist: the compiler AST extractor and a line-oriented Simple CLI scanner. They can disagree and the line scanner depends on ambiguous string indexing.
8. interpreter message substitution repeatedly calls `replace`, making formatting proportional to message length times argument count and allowing unintended textual replacement.
9. current benchmarks do not establish trustworthy before/after gates: timing resolution, corpus construction, operation coverage, and allocation measurements are insufficient.

---

## 2. Scope and non-goals

### 2.1 In scope

- Canonical `text` invariants and the byte/text boundary.
- UTF-8, UTF-16, UTF-32, Latin-1, Windows-1252, and selected legacy East Asian encodings.
- Streaming decoding and encoding through sync and async I/O.
- Efficient parsing of ASCII-heavy and multilingual Simple source.
- Byte, scalar, grapheme, display, UTF-16/LSP, and line/column coordinate conversion.
- Fixed-capacity and dynamically sized text.
- SIMD validation, transcoding, search, scanning, and ASCII transforms.
- Unicode normalization, segmentation, case mapping, identifiers, and security diagnostics.
- Simple language i18n syntax, extraction, catalogs, typed placeholders, plural/select, fallback, and no-allocation deployment.
- Differential tests, fuzzing, benchmarks, migration rules, and parallel implementation work.

### 2.2 Deliberate non-goals

- Automatically normalizing every string.
- Making grapheme clusters the default unit for compiler, protocol, or storage APIs.
- Inferring file encodings heuristically in the core I/O API.
- Localizing Simple keywords by default.
- Giving `text[i]` an expensive hidden Unicode meaning.
- Embedding a complete MessageFormat parser into every ordinary string-literal scan.
- Making terminal display width a property of a Unicode string independent of terminal policy.
- Replacing large-document editor data structures with the general small-string representation.

---

## 3. Precise terminology and coordinate model

| Term | Definition | Example for `Aé‍` |
|---|---|---:|
| Byte | One UTF-8 code unit | 14 bytes |
| Unicode code point | Integer in the Unicode code space, including surrogate values that are not scalar values | Not a safe runtime text element by itself |
| Unicode scalar value | Code point excluding surrogate range | `A`, `é`, ``, ZWJ, ``: 5 scalars |
| Extended grapheme cluster | User-perceived editing unit under UAX #29 | `A`, `é`, `‍`: 3 clusters |
| Display cell | Terminal/layout width under a selected policy | Context-dependent; not universally derivable from cluster count |
| Native index | Offset in the underlying storage encoding | UTF-8 byte offset for `text` |
| Scalar ordinal | “Nth scalar” from the start | Requires scanning or an index |
| Text boundary index | Native byte offset proven to be a scalar boundary | Can move next/previous in O(1) local work |

The key design principle is that these coordinates are not interchangeable integers. A byte offset is ideal for storage, slicing, compiler spans, and native APIs. A scalar ordinal is useful for algorithmic requests such as “the 100th scalar.” A grapheme index is appropriate for UI cursor behavior. A display-cell position belongs to rendering policy. LSP may request UTF-16 code-unit positions even when the compiler stores UTF-8.

---

## 4. Repository audit at the pinned snapshot

This audit is based on `ormastes/simple` commit [`112ac2030f0c5c442c480cb0e86916402e5c5eeb`](https://github.com/ormastes/simple/tree/112ac2030f0c5c442c480cb0e86916402e5c5eeb).

### 4.1 Runtime and core string representation

The newer runtime already points in the right direction:

- [`src/runtime/runtime_simd_dispatch.h`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/runtime/runtime_simd_dispatch.h) defines a compact runtime string header, ASCII and cached-code-point-count metadata, runtime CPU dispatch, validation, search, equality, and ASCII case operations.
- [`src/runtime/simple_core/core_string.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/runtime/simple_core/core_string.spl) uses a 16-byte header followed by bytes and a NUL terminator. Its scalar access path scans from the beginning, so repeated ordinal access can become quadratic.
- [`src/runtime/runtime.h`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/runtime/runtime.h) still exposes legacy C-shaped string surfaces, which makes ABI consistency and invariant enforcement important.

**Decision:** retain this UTF-8 primitive and improve it. Do not implement the older proposal as a second, competing heap object.

### 4.2 Standard-library string correctness

The byte-oriented foundations are useful, but several APIs expose them as character semantics:

| Location | Current behavior | Problem | Required action |
|---|---|---|---|
| [`src/lib/common/string_core.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/string_core.spl) | `str_slice` slices bytes directly | Endpoints may split a scalar | Add checked boundary API; retain explicitly named unsafe/byte variant only |
| same | `str_char_at(s, idx)` returns `s[idx:idx+1]` | A continuation or lead byte can become malformed `text` | Rename legacy operation to `byte_at`; implement scalar access returning a scalar value or valid slice |
| same | trim/case/reverse/split helpers are predominantly ASCII/byte-oriented | Names imply broader Unicode behavior | Split ASCII and Unicode APIs and document complexity |
| same | `char_code_inline` is ASCII-only | Ambiguous name | Rename to `ascii_code` or return typed error outside ASCII |
| same | `rt_bytes_to_text` copies bytes without validation | Violates canonical valid-UTF-8 invariant | Make unsafe/internal; add checked and explicit lossy constructors |
| [`src/lib/common/text.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/text.spl) | JSON escaping tracks byte offsets because `len`/substring and `chars()` use different units | Correct local workaround, but evidence of API ambiguity | Preserve optimized run-copy strategy; migrate to explicit byte cursor/view APIs |

The current library has already learned an important performance lesson: repeated one-character concatenation created superlinear behavior, and several helpers were rewritten to collect and join segments. That work should be retained as a correctness oracle, but a linear `TextBuilder` should replace recursive batch concatenation as the normal construction primitive.

### 4.3 Encoding modules

[`src/lib/common/encoding/utf8.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/utf8.spl) already states that internal text is UTF-8 and provides scalar reference operations, validation, code-point counting, safe truncation, and cached ASCII/count metadata. This is the correct architectural anchor.

The generic path is less suitable for production:

| Module | Finding | Consequence |
|---|---|---|
| [`utf16.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/utf16.spl) | Converts through arrays of integer code points | Extra allocation, memory traffic, and two-pass decoding/encoding |
| [`codec.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/codec.spl) | Generic transcoding decodes to an intermediate code-point array | Prevents streaming and adds large transient memory |
| same | Unknown names can fall back to UTF-8 | Silent misdecoding/security risk | Unknown labels must be an error |
| same | Byte-by-byte text reconstruction treats high UTF-8 bytes independently | Multibyte input can be corrupted/replaced multiple times | Replace with direct validated builder append |
| same | ASCII replacement is performed by input byte rather than decoded scalar | One non-ASCII scalar can emit several replacement markers | Replacement policy operates on malformed sequence/scalar, not byte |
| [`text_ops.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/text_ops.spl) | “UTF-8 mode” behaves as byte mode and “FullUnicode” scans scalars | Encoding and coordinate policy are conflated | Replace global modes with explicit byte/scalar/grapheme APIs |
| [`char_mode.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/char_mode.spl) | Mutable global mode | Not thread-safe, composable, or locally reviewable | Remove from core semantics; keep only temporary compatibility facade |

### 4.4 Indexing implementation

[`src/lib/common/encoding/width_index.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/width_index.spl) exposes lazy index and rank/select-shaped APIs. The Rust backend in [`src/compiler_rust/runtime/src/value/utf8_kernels.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/runtime/src/value/utf8_kernels.rs) currently stores every scalar start as `Vec<usize>` and registers it in a process-global `Mutex<HashMap<handle, index>>`.

That implementation has four problems:

1. memory is O(number of scalars), often 8 bytes per scalar on 64-bit hosts;
2. creation scans the entire text and allocates even if only a few positions are queried;
3. handle lookup and global locking add overhead and lifetime hazards;
4. the rank/select names imply a succinct representation, but the implementation is a full position table.

**Decision:** replace it with an owner-bound RAII `IndexedText` and sparse checkpoints. Keep full position tables only as a separately named benchmark option for workloads where memory is acceptable and measured latency requires them.

### 4.5 SIMD backend parity

[`doc/03_plan/compiler/simd_opt/simd_utf8_text_api_optimization.md`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/doc/03_plan/compiler/simd_opt/simd_utf8_text_api_optimization.md) records the SIMD text plan as complete, including full validation and indexing claims. The current Rust implementation does not fully match those claims: its AVX2/NEON paths identify an ASCII prefix and then fall back to scalar validation/counting for the remainder, and its “rank/select” implementation is the full start-offset vector described above.

This is a **documentation-to-runtime parity defect**, not merely an optimization opportunity. The completion matrix must be reopened and tested per backend and per operation. “A function exists” is not evidence that the intended algorithm is implemented.

### 4.6 I/O surface

[`src/lib/common/io/traits.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/io/traits.spl) mixes byte methods (`read`, `read_all`) with text methods (`read_text`, `read_line`) in the same low-level trait. Its example converts arbitrary bytes using unchecked `rt_bytes_to_text`.

The byte source must remain authoritative. Text decoding belongs in a composable decoder reader that carries encoding state across chunks. Otherwise, a UTF-8 sequence, UTF-16 surrogate pair, or stateful legacy sequence split at a read boundary cannot be handled correctly.

### 4.7 Compiler and lexer

The Rust lexer in [`src/compiler_rust/parser/src/lexer/mod.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/parser/src/lexer/mod.rs) uses `&str` and `CharIndices`, which guarantees valid UTF-8 and keeps `current_pos` in bytes. This is a sound span model. However, every token path pays scalar-iteration overhead, including ASCII syntax.

Specific findings:

- [`strings.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/parser/src/lexer/strings.rs) creates new `String` buffers and pushes one scalar at a time. F-string failure paths clone lexer state and literal buffers.
- `scan_string_unit_suffix()` uses byte length to decide how many character-iterator advances to perform. A non-ASCII suffix can advance too far.
- [`i18n.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/parser/src/lexer/i18n.rs) duplicates much of ordinary/f-string scanning and builds interpolation expression strings instead of retaining source spans.
- [`identifiers.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/parser/src/lexer/identifiers.rs) uses broad language-library alphanumeric tests rather than a pinned UAX #31 XID profile and does not define NFC identifier equivalence.

The parser should remain byte-positioned, but the scanner should become byte/block oriented with a non-ASCII slow path.

### 4.8 Current i18n implementation

Simple already supports named source literals such as `Login_failed_"Login failed"` and interpolated forms. The compiler contains an AST extractor, locale-file generator, runtime registry, and interpreter lowering:

- [`src/compiler_rust/compiler/src/i18n/extractor.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/compiler/src/i18n/extractor.rs)
- [`src/compiler_rust/compiler/src/i18n/locale.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/compiler/src/i18n/locale.rs)
- [`src/compiler_rust/compiler/src/i18n/registry.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/compiler/src/i18n/registry.rs)
- [`src/compiler_rust/compiler/src/interpreter/expr/literals.rs`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/compiler/src/interpreter/expr/literals.rs)

This is a useful foundation, but it has production gaps:

| Area | Current design | Required redesign |
|---|---|---|
| Extraction | Explicit named strings plus heuristic extraction of ordinary alphabetic strings | Explicit strings are authoritative; heuristic mode becomes an opt-in audit/lint |
| IDs | Explicit names plus scope/counter auto names | Stable fully qualified ID; never line/counter identity for persisted catalogs |
| Placeholder schema | Collected mainly from identifier interpolation | Compiler-typed argument schema checked across every locale |
| Locale state | Thread-local mutable `String` | Explicit `LocaleContext`; thread-local facade optional only |
| Registry | Nested `HashMap<String, HashMap<String,String>>` | Compiled/memory-mapped catalog keyed by integer `MessageId`; static/perfect-hash profile |
| Lookup | Returns cloned `String` | Borrow catalog data or format directly to a sink/builder |
| Formatting | Repeated textual `replace` | One-pass compiled message IR |
| Plural/select | Not represented as typed catalog logic | CLDR plural/select/message model |
| Error handling | Placeholder/fallback strings | Build-time schema errors, typed runtime errors, deterministic fallback chain |
| No-allocation | Runtime maps and clones | Static catalog and bounded builder profile |

There is also a second extractor in [`src/app/i18n/main.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/app/i18n/main.spl). It scans split lines and indexes strings directly. This implementation should be removed as an independent parser and routed through the compiler AST/extraction service.

### 4.9 Existing design documents to retain and revise

[`doc/05_design/lib/text_i18n/text_encoding_engine.md`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/doc/05_design/lib/text_i18n/text_encoding_engine.md) contains valuable ideas: UTF-8 internal storage, views, builders, legacy East Asian codecs, sparse checkpoints, fixed-capacity text, and Unicode data. Its proposed independent `Text` heap object and 23-byte SSO layout no longer match the newer primitive/runtime architecture.

Retain its behavioral goals, but revise the implementation as follows:

- `text` is the primitive; `TextSlice`, `TextBuilder`, `IndexedText`, and `Utf8Buf<N>` layer on top.
- SSO is a later ABI-and-benchmark decision, not a prerequisite.
- checkpoints are an optional sidecar, not mandatory per-string metadata.
- encoding conversion is streaming and direct rather than code-point-array based.
- locale/message support is compiled and typed, not a property of the base string object.

[`doc/05_design/lib/text_i18n/i18n_init_locale_spec.md`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/doc/05_design/lib/text_i18n/i18n_init_locale_spec.md) should remain the basis for `__init__.spl` and `__init__.{locale}.spl` fallback and generated lookup, with the catalog and type-system changes described later.

### 4.10 Benchmark audit

[`src/lib/gc_async_mut/benchmark/string_bench.spl`](https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/gc_async_mut/benchmark/string_bench.spl) is a useful smoke suite but not a merge gate:

- a microsecond timer is multiplied to report nanoseconds, so sub-microsecond resolution is not real;
- corpora are built with repeated immutable concatenation, contaminating setup cost and stressing the wrong primitive;
- sizes are mostly 1 KiB and 10 KiB;
- allocation counts, cycles/byte, branch misses, memory, binary size, parser throughput, streaming boundaries, and transcoding are absent;
- scalar versus SIMD parity is not recorded as a backend matrix;
- the run-path comment and file location are inconsistent.

No before/after speed numbers are asserted in this report because the requested implementation has not been made and the current suite is not adequate to produce trustworthy regression claims. The implementation plan begins by fixing the measurement infrastructure.

---
## 5. Research findings

### 5.1 Why UTF-8 remains the right internal representation

No single encoding gives constant-time access to every human-perceived character, because Unicode scalar values, combining sequences, emoji ZWJ sequences, and locale/display behavior are distinct problems. Switching internal storage to UTF-32 would make scalar indexing simple but would not make grapheme indexing or display movement constant-time. It would also multiply common ASCII memory use by approximately four and require conversion at almost every modern I/O boundary.

A UTF-8 canonical representation is the best fit for Simple because:

- Simple source, web formats, Unix-like APIs, JSON, and most external text are UTF-8.
- ASCII syntax and identifiers receive one-byte storage and direct byte matching.
- UTF-8 preserves compatibility with byte search and SIMD structural scanning.
- immutable text can expose zero-copy slices when endpoints are validated boundaries.
- the existing runtime, caches, and native dispatch already use UTF-8.
- scalar and grapheme functionality can be added through iterators and views rather than changing storage.

The key is not to claim UTF-8 provides O(1) ordinal character indexing. The architecture should optimize the operations that are common—byte length, ASCII matching, sequential traversal, slicing by known boundaries, search, parsing, and I/O—and make expensive coordinate conversions explicit.

### 5.2 Language and library comparison

| System | Storage/index model | What Simple should adopt | What Simple should not copy blindly |
|---|---|---|---|
| Rust `str` | Valid UTF-8; `len()` is bytes; byte slicing checks scalar boundaries; no integer scalar indexing | Strong validity invariant, explicit iterators, boundary-checked slicing | Rust APIs alone do not solve grapheme/display/i18n needs |
| Go `string` | Immutable bytes by language contract; `range` decodes UTF-8 and yields byte offsets/runes | Fast byte-oriented core and iterator returning native offsets | Go permits arbitrary bytes in `string`; Simple should keep arbitrary bytes separate from valid `text` |
| Swift `String` | Native UTF-8 storage, opaque `String.Index`, ASCII fast paths, breadcrumb indexes for coordinate conversion | Boundary index rather than ordinal integer; lazy breadcrumbs; UTF-8 compiler offsets | Swift’s high-level collection semantics are more complex than Simple needs in the core runtime |
| Python PEP 393 | Per-string 1/2/4-byte canonical representation; scalar indexing O(1) | Evidence that O(1) scalar indexing has substantial representation/ABI complexity | Do not add per-string width variants or duplicate UTF-8 caches to Simple’s base type |
| Julia `String` | UTF-8; indices are native code-unit positions; helpers move to valid boundaries | Native-index semantics and `next`/`previous` movement | Avoid exposing untyped integers that can be invalid boundaries |
| Zig string convention | Byte slices; source UTF-8; decode only where needed | Keep syntax/parser byte-oriented and explicit | Simple needs a stronger valid-text type than a plain byte slice |
| ICU `UText` | Abstract text provider; native indexes use underlying storage; scalar iteration independent of encoding | A provider/view abstraction for contiguous, rope, or external text; native byte indexes for UTF-8 | Avoid bringing a virtual/general abstraction into every small-string operation |
| `encoding_rs` | WHATWG-compatible streaming legacy decoders, FFI-friendly APIs, SIMD UTF-8 support | Mature mapping behavior and streaming boundary design | Do not make browser label quirks the only API; Simple may also expose exact non-web codecs explicitly |
| `simdutf` | Non-allocating validation/transcoding with runtime architecture dispatch | Complete direct kernels, output-size APIs, scalar/error variants, differential testing | Integration must preserve Simple’s noalloc and licensing/build profiles; do not create a second dispatch layer |
| ICU converters | Stateful conversion, explicit callbacks/errors, preflight/buffer APIs | Carry state over split input, strict/replacement policy, converter reuse | Avoid opening a converter by name per call and avoid implicit platform encodings |
| Fluent | Resource-oriented messages, selectors, CLDR plurals, asymmetric localization, bidi isolation | Translator-controlled variants, whole-message formatting, placeholder isolation | Do not require a separate Fluent runtime for the first Simple implementation |
| Unicode MessageFormat | Stable data model/syntax for typed dynamic messages and selectors | Align catalog IR and plural/select semantics for interoperability | Do not put the full grammar in the ordinary source lexer hot path |

#### Sources

- Rust `str`: <https://doc.rust-lang.org/std/primitive.str.html>
- Go strings/runes: <https://go.dev/blog/strings>
- Swift UTF-8 string design: <https://www.swift.org/blog/utf8-string/>
- Python PEP 393: <https://peps.python.org/pep-0393/>
- Julia strings: <https://docs.julialang.org/en/v1/manual/strings/>
- Zig language reference: <https://ziglang.org/documentation/master/>
- ICU UText: <https://unicode-org.github.io/icu/userguide/strings/utext.html>
- `encoding_rs`: <https://github.com/hsivonen/encoding_rs>
- `simdutf`: <https://github.com/simdutf/simdutf>
- ICU conversion: <https://unicode-org.github.io/icu/userguide/conversion/converters.html>
- Project Fluent: <https://projectfluent.org/>
- Unicode MessageFormat: <https://www.unicode.org/reports/tr35/tr35-76/tr35-messageFormat.html>

### 5.3 Efficient conversion from external encodings to UTF-8

#### 5.3.1 Direct transcoding is superior to a code-point-array pipeline

The current generic shape is approximately:

```text
input bytes -> allocate [integer code points] -> decode -> allocate UTF-8 -> encode
```

The recommended shape is:

```text
input chunk -> stateful validating decoder -> append UTF-8 directly to output sink
```

Direct streaming conversion has the following advantages:

- no O(number of scalars) intermediate array;
- less memory traffic and better cache locality;
- supports arbitrarily large streams;
- naturally handles a multibyte sequence split across read boundaries;
- supports fixed-capacity output and partial-progress reporting;
- allows SIMD kernels to write output directly;
- exposes precise input and output offsets for errors.

A scalar reference decoder should remain the normative implementation. Native/SIMD kernels must match it exactly on valid data, malformed prefixes, overlong forms, surrogate values, out-of-range values, incomplete final sequences, and replacement boundaries.

#### 5.3.2 Decoder interface

Illustrative Simple API:

```simple
# Proposed API; names are design-level, not current syntax commitments.
enum DecodeErrorMode:
    Strict
    Replace          # U+FFFD with WHATWG/codec-defined maximal-subpart behavior
    Ignore           # Explicit and discouraged; never default

enum DecodeStatus:
    Complete
    NeedInput
    NeedOutput
    Error(DecodeError)

struct DecodeProgress:
    input_read: i64
    output_written: i64
    status: DecodeStatus

trait TextDecoder:
    me decode_chunk(
        input: ByteSlice,
        output: TextSink,
        final: bool
    ) -> DecodeProgress

    me reset()
```

The decoder owns pending state. UTF-8 needs up to three pending continuation bytes; UTF-16 needs endianness/BOM state and a pending lead surrogate; stateful legacy encodings need their specified decoder state.

`TextSink` should support both a growable `TextBuilder` and a bounded `Utf8Buf<N>`:

```simple
trait TextSink:
    me reserve(additional_bytes: i64) -> Result<(), CapacityError>
    me append_valid_utf8(bytes: ByteSlice) -> Result<(), CapacityError>
    me append_scalar(value: UnicodeScalar) -> Result<(), CapacityError>
```

Only decoder internals and already validated sources may call `append_valid_utf8`. Public arbitrary-byte append must validate.

#### 5.3.3 Encoding-specific fast paths

| Input encoding | Direct UTF-8 strategy | Conservative output bound | SIMD priority |
|---|---|---:|---|
| UTF-8 | ASCII scan + full validation; borrow/adopt bytes when ownership permits | `n` | Highest |
| Latin-1 | ASCII bytes copied; high bytes expanded to two-byte UTF-8 | `2n` | Highest; simple vector classification/packing |
| Windows-1252 | ASCII/vector fast path plus compact exception table for `0x80..0x9F` | `3n` safe; tighter preflight possible | High |
| UTF-16LE/BE | Validate surrogate pairs and encode directly | `3 * code_units` bytes safe | Highest |
| UTF-32LE/BE | Validate scalar range/surrogates and encode directly | `4 * code_units` bytes | High |
| Shift_JIS | ASCII/half-width fast paths plus table/range decoder | Codec-specific | Medium after correctness |
| EUC-KR/Windows-949-compatible mapping | ASCII fast path plus indexed mapping table | Codec-specific | Medium after correctness |
| Big5 | ASCII fast path plus pointer mapping with duplicate/exception rules | Codec-specific | Medium after correctness |
| GB18030 | ASCII, two-byte, and four-byte state machine with range table | Codec-specific | Medium; correctness first |

The WHATWG Encoding Standard is the best compatibility reference for browser/web-facing labels and deployed legacy mappings. For exact file-format codecs, Simple should distinguish exact names where standards differ. In particular, web labels historically associated with ISO-8859-1 decode using Windows-1252 behavior; an explicit `Latin1` codec should retain exact U+0000..U+00FF mapping while `Windows1252` and web-label resolution follow their own semantics.

#### 5.3.4 Strict, replacement, and detection rules

- `Strict` is the default for source code, configuration, protocols, databases, and typed text I/O.
- `Replace` is explicit and suitable for user-facing recovery. It returns replacement count and first-error offset for observability.
- `Ignore` is explicit and should trigger a lint in security-sensitive code.
- An unknown encoding label is an error. It never silently becomes UTF-8.
- Core I/O performs no heuristic encoding detection. UTF BOM detection is allowed when requested.
- Optional charset detection is a separate service returning `(encoding, confidence, evidence)` and must not be treated as proof.
- Source files are UTF-8; an optional UTF-8 BOM may be stripped at ingress. UTF-16/legacy Simple source should require an explicit conversion command rather than hidden compiler behavior.

#### 5.3.5 Reuse versus native implementation

A staged strategy minimizes risk:

1. implement/reference UTF-8, UTF-16LE/BE, UTF-32LE/BE, ASCII, Latin-1 in scalar Simple/Rust/C code;
2. add `simdutf`-equivalent native kernels or integrate a reviewed `simdutf` adapter behind Simple’s existing dispatch;
3. use `encoding_rs` behavior/tables as a differential oracle for WHATWG legacy encodings;
4. generate Simple-owned compact mapping tables from pinned standards data when bootstrapping/no-external-dependency requirements justify it;
5. keep the oracle in tests even after the native implementation is complete.

This avoids making a large third-party runtime mandatory while also avoiding the common failure mode of writing legacy decoders without a complete compatibility oracle.

### 5.4 Efficient parsing of variable-length UTF-8

#### 5.4.1 Keep parser positions in bytes

UTF-8 variable length is not a reason to make the lexer scalar-indexed. Language syntax is mostly ASCII, token spans naturally slice source bytes, and byte offsets interoperate with file maps, memory mapping, hashes, and native parsers. Tree-sitter similarly accepts byte-oriented input and reports byte ranges.

Recommended source-coordinate architecture:

```text
SourceBuffer(valid UTF-8 bytes)
    ├── Token Span: ByteRange
    ├── line starts: [ByteOffset]
    ├── optional per-line UTF-16 breadcrumbs for LSP
    ├── optional scalar/grapheme conversion on diagnostic request
    └── TextSlice views for lexemes
```

The lexer should increment a byte cursor. ASCII bytes are interpreted directly. On a byte with the high bit set, it decodes one scalar and enters the relevant Unicode identifier/literal slow path.

#### 5.4.2 Block-oriented scanner

For ordinary string literals, identifiers, comments, and whitespace, scan 16/32/64-byte blocks for:

- quote delimiters;
- backslash;
- newline/carriage return;
- interpolation braces;
- control bytes;
- non-ASCII bytes.

The exact mask depends on lexical context. For a double-quoted i18n/f-string, the fast block can continue while no byte is one of:

```text
"  \  \n  \r  {  }  or >= 0x80
```

When no special byte exists, advance over the entire block and retain a source slice. When a special byte is found, process the first set bit and resume. This follows the broad design demonstrated by simdjson’s structural stage and `memchr`’s vectorized byte search, without requiring the Simple language parser to become a JSON parser.

#### 5.4.3 Borrow before allocating

Token text should use a source-backed representation:

```simple
union TokenText:
    Borrowed(ByteRange)
    Owned(text)
```

- identifier without normalization/change: borrowed span, interned only when required;
- string without escapes/interpolation: borrowed `TextSlice`;
- string with escapes: allocate once into `TextBuilder`;
- f-string/i18n literal segments: store source spans and decoded owned segments only where escapes require transformation;
- interpolation expression: store source span and invoke the expression parser on that slice rather than building a new string.

This reduces allocation and removes repeated scalar pushes. An AST that must outlive the source buffer can intern or copy at the module boundary, not during each scan step.

#### 5.4.4 Fused validation considerations

If file loading already constructs a validated Rust `&str`/Simple `text`, the parser should not revalidate every token. If a high-throughput parser accepts raw mapped bytes directly, stage 1 may fuse UTF-8 validation with structural scanning. The two entry points should be explicit:

```text
parse_text(validated text)      -> no redundant full validation
parse_utf8_bytes(raw bytes)     -> validate once, then parse
```

Never make “trusted” an untyped boolean. Use a type or internal constructor that proves validation occurred.

#### 5.4.5 Position conversions

For diagnostics and LSP:

- line lookup: binary search line-start byte offsets;
- scalar column: decode from line start, or use a per-line sparse checkpoint for long lines;
- UTF-16 column: count one or two UTF-16 code units per scalar, using lazy breadcrumbs;
- grapheme column: UAX #29 segmentation only when a UI explicitly needs it;
- terminal display column: width policy applied after grapheme segmentation.

Swift’s UTF-8 migration and breadcrumb model demonstrates that UTF-8 storage can coexist efficiently with clients requiring UTF-16 positions.

### 5.5 Efficient movement and random indexing

#### 5.5.1 Use a boundary index, not an ordinal integer, for movement

The fastest general-purpose text index for UTF-8 is a native byte offset known to be at a scalar boundary:

```simple
newtype TextIndex:
    byte: ByteOffset

fn start_index(s: TextView) -> TextIndex
fn end_index(s: TextView) -> TextIndex
fn next_index(s: TextView, i: TextIndex) -> TextIndex
fn previous_index(s: TextView, i: TextIndex) -> TextIndex
fn scalar_at(s: TextView, i: TextIndex) -> UnicodeScalar
fn slice(s: TextView, range: TextRange) -> TextSlice
```

`next_index` inspects the lead byte and advances 1–4 bytes. `previous_index` steps backward over at most three continuation bytes. Both are O(1) local operations. Sequential traversal is O(bytes) total and does not need a side index.

This is closer to Swift’s opaque index and ICU UText’s native index than to “character number.” It answers the user’s “move by index” requirement without adding a hidden O(n) operation to every subscript.

For mutable buffers, indexes must be invalidated by mutation. A debug build can include owner/generation information; optimized immutable `text` indexes can remain a compact byte offset.

#### 5.5.2 Ordinal access is a separate operation

```simple
fn scalar_at_ordinal(s: TextView, ordinal: ScalarIndex) -> Option<UnicodeScalar>
fn byte_offset_of_scalar(s: TextView, ordinal: ScalarIndex) -> Option<ByteOffset>
```

Complexity must be visible:

| Representation | Build | `next/previous` | `nth scalar` | Memory |
|---|---:|---:|---:|---:|
| Plain UTF-8 text | none | O(1) local | O(n) scan | O(1) metadata |
| Sparse checkpoint every `K` scalars | O(n), lazy | O(1) local | O(log(n/K) + K) | O(n/K) offsets |
| Full scalar-start table | O(n) | O(1) | O(1) | O(n) offsets |
| Succinct continuation bitmap + rank/select | O(n) | O(1) local | O(1)/near-O(1) | Approximately one bit/byte plus index overhead |
| Rope with per-node metrics | O(n) construction | O(log chunks) crossing chunks | O(log n + local scan) | Tree/chunk metadata |

Default to plain text. Build a sparse index after repeated ordinal queries or when requested explicitly. The current threshold concept—do not index very small strings—is sound, but the exact byte size and query count must be measured rather than fixed by design intuition.

A practical starting candidate is one checkpoint every 32 or 64 scalars. Each checkpoint stores the native byte offset. For very large text and heavy random access, benchmark a continuation-byte bitmap with rank/select. Succinct structures are valuable research, but they should not be required for the common string path until the implementation demonstrates lower total memory and latency than sparse checkpoints.

#### 5.5.3 Grapheme movement

Grapheme clusters are state-machine boundaries under UAX #29. A `GraphemeCursor` should carry boundary state and move through a `TextView`. Repeated random grapheme ordinals may use a segmented boundary index, but ordinary UI movement should use next/previous boundaries.

Do not make all string indexing grapheme-based. Compiler parsing, protocol fields, hashing, and many algorithms need bytes or scalars, and grapheme definitions evolve with Unicode versions.

### 5.6 Fixed-capacity and variable-length text

A fixed-size Unicode string cannot use “N characters” as a stable storage contract:

- one scalar takes 1–4 UTF-8 bytes;
- one grapheme can contain an unbounded sequence of combining/format scalars;
- normalization can change byte and scalar counts;
- case mapping can expand text;
- localized formatting has data-dependent output length.

Therefore, fixed text capacity is measured in **bytes**:

```simple
struct Utf8Buf<const N: i64>:
    data: [u8; N]
    used: i64

    static fn from_text(s: text) -> Result<Utf8Buf<N>, CapacityError>
    fn as_text() -> TextSlice
    me append(s: TextView) -> Result<(), CapacityError>
    me append_scalar(c: UnicodeScalar) -> Result<(), CapacityError>
    me truncate_at_boundary(max_bytes: i64)
```

`used <= N`, and `data[0:used]` is always valid UTF-8. A failed append does not partially corrupt the invariant. A separate streaming API may return partial progress when explicitly requested.

Recommended fixed family:

- `Bytes<N>`: arbitrary bytes;
- `Ascii<N>`: ASCII-only, useful for stable IDs and protocol tokens;
- `Utf8Buf<N>`: valid UTF-8, dynamic used length;
- `TextBuilder<N>`: formatting façade over `Utf8Buf<N>`;
- `FixedMessageBuffer<N>`: optional alias/profile with truncation policy prohibited by default.

For heap-enabled builds, `TextBuilder` uses geometric capacity growth and finalizes to immutable `text`. For noalloc builds, the same formatting interface targets `Utf8Buf<N>` and returns `CapacityError`.

### 5.7 Large editable text

A flat immutable UTF-8 string remains correct for ordinary values, compiler tokens, logs, paths, and messages. A text editor, large document, or incremental parser has different mutation requirements. It should use a rope or piece tree with:

- UTF-8 chunks sized for cache locality;
- per-node byte length, scalar count, newline count, and optional UTF-16 count;
- chunk boundaries at scalar boundaries;
- local grapheme/line metadata where needed;
- O(log n) coordinate conversion and editing.

Xi Editor’s rope research shows how metrics can map bytes, scalars, and lines through tree summaries. This should be an editor/document library profile, not extra fields on every `text` object.

### 5.8 SIMD opportunities and limits

#### High-value SIMD operations

1. UTF-8 validation and first-error location.
2. ASCII detection and code-point counting by continuation-byte masks.
3. UTF-8 ↔ UTF-16 and Latin-1 → UTF-8 transcoding.
4. byte search for delimiters/newlines/quotes/backslashes.
5. substring search and equality.
6. ASCII case conversion and classification.
7. parser structural masks.
8. JSON/escape scanning and copying unchanged runs.
9. line-start discovery.

#### Operations that remain primarily table/state-machine driven

- full Unicode normalization;
- grapheme/word/sentence segmentation;
- locale-sensitive case mapping;
- collation;
- bidi resolution;
- CLDR plural/message selection.

These operations still benefit from ASCII quick checks, block property lookup, fewer branches, generated compact tables, and vectorized “all ordinary” tests. They should not be advertised as SIMD-complete merely because an ASCII prefix is vectorized.

#### Dispatch architecture

Simple already has native dispatch. Extend that one dispatch point rather than layering separate dispatch inside each library:

```text
scalar portable reference
    ├── x86 SSE4.2/AVX2/AVX-512 implementation
    ├── AArch64 NEON/SVE implementation
    ├── RISC-V V implementation when available
    └── compile-time tiny scalar profile
```

Each operation has a minimum-size threshold. Small strings often run faster in a branch-light scalar path than through dispatch and vector setup. Thresholds are benchmark output, not constants copied from another library.

#### Research evidence

- Keiser and Lemire, *Validating UTF-8 In Less Than One Instruction Per Byte*: <https://arxiv.org/abs/2010.03090>
- Lemire and Muła, *Transcoding Billions of Unicode Characters per Second with SIMD Instructions*: <https://arxiv.org/abs/2109.10433>
- Clausecker and Lemire, *Transcoding Unicode Characters with AVX-512 Instructions*: <https://arxiv.org/abs/2212.05098>
- Langdale and Lemire, *Parsing Gigabytes of JSON per Second*: <https://arxiv.org/abs/1902.08318>
- `simdutf`: <https://github.com/simdutf/simdutf>
- `simdjson`: <https://github.com/simdjson/simdjson>
- Rust `memchr`: <https://github.com/BurntSushi/memchr>

### 5.9 Unicode algorithms and versioning

Simple should pin generated Unicode data and expose its version at runtime/build metadata. The first implementation target in this report is Unicode 17.0.0.

| Function | Standard/data | Default behavior |
|---|---|---|
| Identifier syntax | UAX #31 XID profile | XID_Start/XID_Continue plus `_`, normalized to NFC for symbol identity |
| Normalization | UAX #15 | Explicit `normalize`; no automatic normalization of arbitrary text |
| Grapheme/word/sentence boundaries | UAX #29 | Explicit iterators/views |
| Line breaking | UAX #14 | Layout library, not base `text` |
| Bidirectional layout | UAX #9 | UI/message formatting layer |
| Security diagnostics | UTS #39 | Confusable/mixed-script/bidi warnings; stricter mission-critical mode |
| Locale identifiers/data | BCP 47 + CLDR/LDML | Parsed `LocaleId`; pinned CLDR data |
| Plural rules | CLDR | Cardinal/ordinal selectors in catalog compiler |
| Collation | CLDR/Unicode collation data | Optional locale capability; never byte equality |

#### Normalization policy

- byte equality remains the default `text` equality and hash contract;
- source identifiers are normalized to NFC for symbol identity after validation;
- string literal contents preserve the exact Unicode scalar sequence written by the author, except escape decoding;
- file paths preserve platform semantics; do not normalize silently;
- provide `is_normalized(form)`, `normalize(form)`, and a `NormalizedText<Form>` proof wrapper where repeated normalized operations justify it;
- compatibility normalization (`NFKC/NFKD`) is opt-in and must not be used blindly for user content.

#### Display width policy

The current hardcoded width ranges are not a complete Unicode width algorithm. A terminal width function must specify:

- Unicode data version;
- East Asian Ambiguous width policy;
- emoji presentation policy;
- handling of controls, combining marks, ZWJ sequences, variation selectors, and unassigned scalars;
- terminal compatibility mode.

A GUI does not normally use terminal cells; it shapes grapheme sequences with fonts. Therefore `display_width()` must live in a terminal/layout module, not define `text.len()`.

### 5.10 Internationalized message research

A localization system must translate whole messages, not concatenate translated fragments. ICU recommends keeping variable elements inside a single message so translators can reorder them. CLDR plural rules are not reducible to singular/plural; locales may use `zero`, `one`, `two`, `few`, `many`, and `other`. Fluent demonstrates asymmetric localization, where a simple source message can become a selector-rich translation without forcing the source locale to contain the same grammatical complexity.

Unicode MessageFormat became a stable part of CLDR in CLDR 47. The report pins the CLDR 48/48.2 specification family and CLDR 48.2.1 data update. Simple does not need to expose the full standard syntax immediately, but its internal message data model should be able to represent:

- literal text;
- typed external variables;
- local variables;
- function/formatter calls;
- plural and exact-number matching;
- string/select matching;
- fallback variants;
- bidi isolation around substitutions;
- attributes/related UI strings if later required.

Useful references:

- Unicode MessageFormat working group: <https://github.com/unicode-org/message-format-wg>
- LDML Part 9, MessageFormat: <https://www.unicode.org/reports/tr35/tr35-76/tr35-messageFormat.html>
- CLDR plural rules: <https://www.unicode.org/cldr/charts/latest/supplemental/language_plural_rules.html>
- ICU message formatting guidance: <https://unicode-org.github.io/icu/userguide/format_parse/messages/>
- Fluent selectors: <https://projectfluent.org/fluent/guide/selectors.html>
- Fluent bidi strategy background: <https://github.com/projectfluent/fluent/wiki/BiDi-in-Fluent>

---
## 6. Proposed Simple text architecture

### 6.1 Architectural layers

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│ Applications: compiler, IDE, UI, server, database, office, firmware        │
├─────────────────────────────────────────────────────────────────────────────┤
│ i18n: LocaleContext, MessageId, compiled catalog, plural/select, formatters │
├─────────────────────────────────────────────────────────────────────────────┤
│ Unicode services: normalization, segmentation, case, bidi, collation       │
├─────────────────────────────────────────────────────────────────────────────┤
│ Text views: TextSlice, TextIndex, TextCursor, IndexedText, GraphemeView     │
├─────────────────────────────────────────────────────────────────────────────┤
│ Construction: TextBuilder, Utf8Buf<N>, decoder/encoder sinks               │
├─────────────────────────────────────────────────────────────────────────────┤
│ Canonical primitive: immutable validated UTF-8 `text`                      │
├─────────────────────────────────────────────────────────────────────────────┤
│ Bytes and I/O: [u8], ByteSlice, Read/Write, mapped input                    │
├─────────────────────────────────────────────────────────────────────────────┤
│ Kernels: portable scalar oracle + architecture-selected SIMD               │
└─────────────────────────────────────────────────────────────────────────────┘
```

The upper layers may be excluded by profile. The primitive and scalar UTF-8 validation remain available in tiny builds. Unicode tables, legacy codecs, collation, bidi, and dynamic catalogs are capability modules.

### 6.2 Canonical `text` invariant

A value of type `text` guarantees:

1. its payload is structurally valid UTF-8;
2. no encoded surrogate scalar exists;
3. no scalar exceeds U+10FFFF;
4. its byte length is known in O(1);
5. immutable payload bytes do not change for the value’s lifetime;
6. slicing as `text` occurs only at UTF-8 boundaries;
7. equality and hash are byte-exact unless another API explicitly requests normalization/collation/case folding.

A NUL byte is a valid Unicode scalar U+0000 and may occur inside `text`; the runtime’s trailing NUL is a compatibility terminator, not the authoritative length. C FFI APIs must always receive pointer plus length unless a checked “no interior NUL” adapter is used.

### 6.3 Constructors

```simple
# Proposed semantic surface.
fn text_from_utf8(bytes: ByteSlice) -> Result<text, Utf8Error>
fn text_from_utf8_lossy(bytes: ByteSlice) -> LossyTextResult
fn text_from_ascii(bytes: ByteSlice) -> Result<text, AsciiError>
fn text_from_scalar(c: UnicodeScalar) -> text

unsafe fn text_from_utf8_unchecked(
    bytes: ByteSlice,
    proof: Utf8ValidationProof
) -> text
```

`text_from_utf8_unchecked` is runtime/compiler internal. A plain `unsafe bool` is not enough; the call site should carry a proof/result produced by validation or construction.

`rt_bytes_to_text` should be split:

- checked public constructor;
- explicit lossy constructor;
- private trusted constructor used only after validation.

### 6.4 Length and emptiness

```simple
fn byte_len(s: TextView) -> i64          # O(1) for flat text/slice
fn scalar_len(s: TextView) -> i64        # cached or O(n)
fn grapheme_len(s: TextView) -> i64      # O(n), or cached view
fn utf16_len(s: TextView) -> i64         # O(n), optional source-map cache
fn is_empty(s: TextView) -> bool         # byte_len == 0
fn is_ascii(s: TextView) -> bool         # cached/SIMD
```

Compatibility rule:

- existing `s.len()` remains byte length until a versioned language-edition decision;
- new standard-library and compiler code uses `byte_len()` or the intended explicit unit;
- a lint warns when `.len()` participates in character-sensitive indexing, truncation, UI layout, or iteration.

Redefining `.len()` immediately would silently alter loops, buffer sizing, file offsets, FFI, parser spans, and performance assumptions. A clean future edition may reserve `.len()` for an explicitly documented unit, but migration should not guess.

### 6.5 Scalar value type

Use a distinct scalar type rather than representing a Unicode scalar as a one-character `text`:

```simple
newtype UnicodeScalar:
    value: u32

static fn UnicodeScalar.from_u32(v: u32) -> Result<UnicodeScalar, ScalarError>
fn UnicodeScalar.to_u32() -> u32
fn UnicodeScalar.encode_utf8(self, out: TextSink) -> Result<(), CapacityError>
```

A scalar excludes `0xD800..0xDFFF` and values above `0x10FFFF`. A code-point type including surrogate values may exist only for low-level Unicode-data tooling and must not enter `text`.

### 6.6 Views and slices

```simple
trait TextView:
    fn bytes() -> ByteSlice
    fn byte_len() -> i64
    fn is_ascii() -> bool

struct TextSlice with TextView:
    owner: text
    start: ByteOffset
    end: ByteOffset
```

The concrete representation may retain the owner or use a lifetime/borrow, depending on Simple’s final borrow/runtime model. Semantics are more important than the exact storage.

APIs:

```simple
fn slice_bytes(s: TextView, r: ByteRange) -> Result<TextSlice, BoundaryError>
unsafe fn slice_bytes_unchecked(s: TextView, r: ByteRange, proof: BoundaryProof) -> TextSlice
fn prefix_bytes(s: TextView, max: i64) -> TextSlice      # backs up to boundary
fn suffix_bytes(s: TextView, max: i64) -> TextSlice      # advances to boundary
fn split_at_index(s: TextView, i: TextIndex) -> (TextSlice, TextSlice)
```

For binary/protocol algorithms that intentionally split arbitrary bytes, call `s.bytes().slice(...)`; the return type is bytes, not `text`.

### 6.7 Index and cursor model

```simple
newtype ByteOffset: i64
newtype ScalarIndex: i64
newtype GraphemeIndex: i64
newtype Utf16Offset: i64
newtype DisplayCell: i64

struct TextIndex:
    byte: ByteOffset

struct TextRange:
    start: TextIndex
    end: TextIndex

struct TextCursor:
    source: TextView
    index: TextIndex
```

Core operations:

```simple
fn TextCursor.current() -> Option<UnicodeScalar>
me fn TextCursor.next() -> Option<UnicodeScalar>
me fn TextCursor.previous() -> Option<UnicodeScalar>
me fn TextCursor.move_scalars(delta: i64) -> Result<(), BoundsError>
me fn TextCursor.seek(index: TextIndex)
fn TextCursor.byte_offset() -> ByteOffset
```

For an immutable contiguous `text`, moving one scalar is bounded by examining at most four bytes. `move_scalars(k)` is O(|k|), which is clear from the verb. `scalar_at_ordinal(n)` uses a scan or `IndexedText` and should not be disguised as ordinary subscript syntax.

### 6.8 Iterators

```simple
fn bytes(s: TextView) -> ByteIterator
fn scalars(s: TextView) -> ScalarIterator
fn scalar_indices(s: TextView) -> Iterator<(TextIndex, UnicodeScalar)>
fn graphemes(s: TextView) -> GraphemeIterator
fn lines(s: TextView, policy: LinePolicy = Universal) -> LineIterator
```

`scalar_indices` provides the native boundary index with each scalar, equivalent to the useful part of Go’s `range` but with valid-text guarantees.

`lines` should define its separators. A compiler-source policy typically recognizes LF and CRLF. A general Unicode policy may also recognize NEL, line separator, and paragraph separator. Do not hide this difference.

### 6.9 Optional indexed view

```simple
struct IndexedText:
    value: text
    index: SparseScalarIndex

struct SparseScalarIndex:
    stride: u16
    scalar_count: i64
    checkpoints: [ByteOffset]
```

Construction policy:

```simple
fn text.indexed(stride: i64 = auto) -> IndexedText
fn text.auto_indexed(access_hint: TextAccessHint) -> IndexedText
```

Suggested adaptive behavior, subject to benchmarks:

- below 256 bytes: never build;
- one or two ordinal queries: scan;
- repeated queries: build sparse checkpoints;
- select stride from text length/cache profile, initially benchmark 32 and 64 scalars;
- ASCII-only text needs no offsets because scalar ordinal equals byte offset;
- full table and succinct rank/select are explicitly selectable experimental backends.

The index is owned by the wrapper. There is no process-global handle map. If shared cache reuse is later desired, use an immutable owner-attached sidecar with safe lifetime and weak reclamation, not numeric handles manually freed by callers.

### 6.10 Builder

```simple
struct TextBuilder:
    buffer: ByteBuffer

static fn TextBuilder.with_capacity(bytes: i64) -> TextBuilder
me fn append(s: TextView)
me fn append_ascii(s: AsciiView)
me fn append_scalar(c: UnicodeScalar)
me fn append_escaped(s: TextView, policy: EscapePolicy)
me fn reserve(bytes: i64)
fn byte_len() -> i64
me fn finish() -> text
```

Builder rules:

- maintain valid UTF-8 after every public operation;
- allow private unchecked run copy only from proven-valid text;
- geometric growth in heap profile;
- checked bounded growth in `Utf8Buf<N>` profile;
- no repeated immutable concatenation in loops;
- formatting APIs write to a `TextSink` rather than returning temporary strings for each segment.

The compiler can lower chained literal concatenation to one capacity calculation and builder operation. For unknown lengths, it can use amortized growth.

### 6.11 Representation and ABI plan

#### Phase 1: preserve current ABI

Keep the existing runtime header, trailing NUL, length, ASCII flag, and cached scalar count. Do not overload the remaining bits with normalization, grapheme, or locale state. Those properties are version-dependent or potentially expensive and belong in wrappers/sidecars.

Advantages:

- low migration risk across C, Rust, compiler, interpreter, runtime, and generated code;
- existing ASCII/count cache remains useful;
- SIMD dispatch and native functions continue to operate on the same payload;
- no immediate binary-size or object-size increase.

#### SSO decision

The older design’s small-string optimization may reduce allocations, but it is not automatically compatible with the current header and FFI assumptions. Evaluate it only after:

1. allocation profiling shows short strings dominate important workloads;
2. a representation can preserve pointer/length APIs and move/copy semantics;
3. interpreter/compiler/runtime code size and branch cost are measured;
4. tiny/noalloc profiles are compared against `Utf8Buf<N>` and literal interning;
5. ABI versioning is planned.

Until then, improve literal interning, builders, allocation arenas, and fixed-capacity types without changing every `text` value.

### 6.12 Byte and ASCII APIs

Many high-performance algorithms are correctly byte-oriented. They should become explicit rather than removed:

```simple
fn byte_at(s: TextView, i: ByteOffset) -> Option<u8>
fn find_byte(s: TextView, b: u8) -> Option<ByteOffset>
fn find_ascii(s: TextView, needle: AsciiView) -> Option<ByteOffset>
fn starts_with_bytes(s: TextView, prefix: ByteSlice) -> bool
fn ascii_eq_ignore_case(a: TextView, b: TextView) -> bool
fn to_ascii_lower(s: TextView) -> Result<text, NonAsciiError>
```

`find` of a valid UTF-8 substring can remain byte search because UTF-8 is self-synchronizing: a valid encoded scalar sequence cannot begin at a continuation byte as the same valid substring. Results are native byte offsets and therefore valid boundaries when the needle is valid text.

### 6.13 Unicode operation surface

```simple
# Explicit normalization
fn is_normalized(s: TextView, form: NormalizationForm) -> bool
fn normalize(s: TextView, form: NormalizationForm = NFC) -> text
fn canonical_eq(a: TextView, b: TextView) -> bool

# Case
fn to_lower(s: TextView, locale: Option<LocaleId> = None) -> text
fn to_upper(s: TextView, locale: Option<LocaleId> = None) -> text
fn case_fold(s: TextView) -> text
fn case_insensitive_eq(a: TextView, b: TextView) -> bool

# Segmentation
fn graphemes(s: TextView) -> GraphemeIterator
fn words(s: TextView, locale: Option<LocaleId> = None) -> WordIterator
fn sentences(s: TextView, locale: Option<LocaleId> = None) -> SentenceIterator

# Collation, optional capability
fn collator(locale: LocaleId, options: CollationOptions) -> Collator
fn Collator.compare(a: TextView, b: TextView) -> Ordering
```

ASCII-specialized APIs remain available and faster. Unicode operations must document whether they can expand output and whether they are locale-neutral or locale-sensitive.

### 6.14 Unicode data generation

Add a deterministic generator that consumes pinned Unicode Character Database and CLDR inputs and emits:

- compact property tries/range tables;
- decomposition/composition mappings;
- case mappings/folding;
- UAX #29 break properties/state tables;
- XID_Start/XID_Continue;
- confusable skeleton data for optional diagnostics;
- East Asian width/emoji properties for terminal policy;
- plural-rule bytecode/data;
- locale fallback/likely-subtag data as required.

Generated files include:

```text
unicode_version = "17.0.0"
cldr_version = "48.2.1"
generator_version = <hash/version>
input_hashes = {...}
```

The generator output is split by capability so a compiler-only or embedded build does not link collation and full locale data.

### 6.15 Source-language Unicode support

#### Source encoding

- `.spl` source is UTF-8.
- invalid UTF-8 is a compile error with exact byte offset and nearby escaped bytes.
- optional UTF-8 BOM is accepted only at byte offset zero and not part of source spans.
- newline normalization is not performed on the source buffer; lexer recognizes configured line endings while preserving byte spans.

#### Identifiers

Recommended profile:

```text
start    := '_' | XID_Start
continue := '_' | XID_Continue
identity := NFC(identifier scalar sequence)
keywords := ASCII spellings only
```

Implementation fast path:

1. ASCII `[A-Za-z_]` starts identifier;
2. ASCII `[A-Za-z0-9_]` continues;
3. high-bit byte invokes UTF-8 scalar decode and pinned XID table;
4. only identifiers containing non-ASCII or non-NFC quick-check failures allocate/normalize;
5. intern the normalized symbol; retain original spelling span for diagnostics.

Security diagnostics:

- mixed-script identifiers;
- confusable skeleton collision in the same scope/module;
- invisible/default-ignorable characters;
- bidi controls and unbalanced isolates/embeddings;
- normalization-equivalent duplicate spellings.

Default severity is warning except structurally dangerous bidi/control cases. Mission-critical mode may make them errors. Backtick-escaped identifiers can permit otherwise disallowed spellings where interoperability requires them, but symbol identity and security rules remain explicit.

#### String and character literals

- string literal result is valid UTF-8 `text`;
- `\u{...}` produces a Unicode scalar and rejects surrogates/out-of-range values;
- raw literals preserve source scalar sequence;
- ordinary literal escapes are decoded once into a builder;
- a scalar literal returns `UnicodeScalar`, not a one-byte/one-string pseudo-character;
- localized strings use the same literal scanner plus message metadata; do not maintain a separate escape implementation.

### 6.16 Parser redesign

#### Scanner state

Replace the core character iterator with a byte cursor over a valid source buffer:

```rust
// Illustrative Rust-side shape.
struct Lexer<'a> {
    source: &'a str,
    bytes: &'a [u8],
    pos: usize,              // byte offset
    line: usize,
    line_start: usize,       // byte offset
    // indentation and bracket state unchanged
}
```

Operations:

- `peek_byte`, `advance_ascii`, `decode_scalar_at`, `find_any_special`;
- ASCII token tables and keyword matching operate on borrowed byte slices;
- Unicode identifiers enter a scalar slow path;
- source columns are not updated scalar by scalar unless diagnostics require eager columns; line starts are authoritative.

This avoids maintaining two cursor abstractions (`CharIndices` plus byte offset) and makes block scanning straightforward.

#### Unified string scanner

Use one configurable scanner:

```text
StringScanConfig
    quote: single | double | triple
    escapes: none | raw-quote-only | standard
    interpolation: none | braces
    i18n_key: optional MessageKey
    multiline: bool
    suffix: allowed | forbidden
```

The scanner returns:

```text
StringToken
    raw_span
    literal_segments: [BorrowedSpan | DecodedText]
    interpolation_spans: [ByteRange]
    flags: escaped, multiline, localized, typed_suffix
```

Benefits:

- one escape implementation;
- one brace-depth/interpolation implementation;
- fewer clones and divergent bugs;
- ASCII block fast path shared by ordinary, raw, f-string, and i18n forms;
- exact spans for extraction and diagnostics.

F-string/i18n backtracking should restore byte positions and segment counts, not clone potentially large strings and the entire lexer iterator. Ambiguous literal-brace behavior should be resolved by grammar where possible; otherwise use a small checkpoint struct.

#### Parser benchmark targets

Measure independently:

- lex only;
- parse without lowering;
- full frontend;
- files with no strings;
- ASCII literals;
- escaped literals;
- multilingual literals;
- i18n strings and nested interpolation;
- huge comments/docstrings;
- long Unicode identifiers;
- malformed UTF-8 ingress and malformed escapes.

ASCII-heavy source must not regress materially because i18n exists. Non-ASCII source should improve by borrowing runs and avoiding per-scalar allocation.

---

## 7. I/O and codec architecture

### 7.1 Separate bytes from decoded text

Replace low-level mixed traits with layered composition:

```simple
trait Read:
    me read(output: ByteBuffer) -> Result<i64, IoError>

trait Write:
    me write(input: ByteSlice) -> Result<i64, IoError>

class TextReader<R: Read, D: TextDecoder>:
    reader: R
    decoder: D
    input_buffer: ByteBuffer
    text_buffer: TextBuilder

class TextWriter<W: Write, E: TextEncoder>:
    writer: W
    encoder: E
```

Convenience APIs:

```simple
fn Read.read_text(
    encoding: Encoding = UTF8,
    errors: DecodeErrorMode = Strict
) -> Result<text, TextIoError>

fn Read.text_reader(
    encoding: Encoding = UTF8,
    errors: DecodeErrorMode = Strict
) -> TextReader

fn Write.write_text(
    value: TextView,
    encoding: Encoding = UTF8,
    errors: EncodeErrorMode = Strict
) -> Result<(), TextIoError>
```

`read_text_lossy()` is separately named. There is no unchecked default.

### 7.2 Streaming line reading

`TextReader.read_line()` operates on decoded text and maintains decoder state. It must handle:

- UTF-8 sequence split across byte chunks;
- UTF-16 code unit/surrogate pair split across chunks;
- CRLF split across chunks;
- selected Unicode line separators under policy;
- final line without terminator;
- strict decode error with absolute input offset.

A UTF-8-specialized reader can scan for `0x0A` with SIMD while also validating. For other encodings, use encoding-aware code-unit scans only when guaranteed safe, otherwise decode through the normal streaming path.

### 7.3 Error model

```simple
struct DecodeError:
    encoding: Encoding
    absolute_byte_offset: i64
    chunk_byte_offset: i64
    kind: DecodeErrorKind
    offending: Bytes<8>
    pending_state: DecodeStateSummary

struct LossyTextResult:
    value: text
    replacements: i64
    first_error: Option<DecodeError>
```

The error must distinguish invalid sequence, incomplete final sequence, isolated surrogate, out-of-range scalar, unmappable byte sequence, and output capacity exhaustion.

### 7.4 File API policy

- `file_read_bytes(path)` is always available.
- `file_read_text(path)` means strict UTF-8.
- `file_read_text(path, encoding=...)` is explicit transcoding.
- platform “default encoding” is not used silently.
- source/compiler/config/package manifests use strict UTF-8.
- user-import workflows may call a detector first, show confidence, and then decode explicitly.

### 7.5 Async and zero-copy considerations

The decoder state is independent of sync/async transport. Async readers feed the same `decode_chunk` interface.

For UTF-8 input:

- if the full owned byte buffer validates, the runtime may adopt it as `text` without copying when allocator/layout contracts permit;
- a borrowed valid range becomes `TextSlice`;
- mapped read-only files can be wrapped as a source-specific text owner after validation;
- streaming output still uses a builder when chunk ownership cannot be joined zero-copy.

For non-UTF-8 input, conversion necessarily writes UTF-8 output, but it should write once.

### 7.6 Codec registry and profiles

```simple
enum Encoding:
    UTF8
    UTF16LE
    UTF16BE
    UTF32LE
    UTF32BE
    ASCII
    Latin1
    Windows1252
    ShiftJIS
    EUCKR
    Big5
    GB18030
```

Aliases are resolved by a separate canonical-label function. Web profile follows WHATWG labels; exact profile accepts explicit canonical codec names. Unsupported codecs return `UnsupportedEncoding`, not UTF-8 fallback.

Profiles:

| Profile | Included codecs |
|---|---|
| `text_tiny` | UTF-8, ASCII |
| `text_core` | UTF-8, UTF-16, UTF-32, ASCII, Latin-1 |
| `text_desktop` | Core + Windows-1252 + selected East Asian codecs |
| `text_web` | WHATWG encoding label/mapping set |
| `text_full` | Desktop/web plus optional platform codecs |

---
## 8. Simple language i18n architecture

### 8.1 Preserve the current ergonomic syntax

Simple already has a concise explicit marker:

```simple
Login_failed_"Login failed"
Welcome_"Hello, {name}!"
```

Keep that syntax. It gives the compiler an explicit stable key and keeps ordinary strings free of localization overhead. Do not change every string literal into a locale-aware object.

The semantic result is not “a special encoded string.” The compiler lowers a localized expression to a message lookup/format operation whose final output is ordinary UTF-8 `text`:

```text
Name_"default"              -> format_message(MessageId(Name_), no_args, default)
Name_"...{arg}..."          -> format_message(MessageId(Name_), typed_args, default_ir)
```

The optimizer can resolve the operation differently by build profile.

### 8.2 Message keys

Message keys should be stable and resistant to confusable/catalog churn:

- default spelling profile: ASCII identifier components plus `_`;
- explicit source name is authoritative;
- fully qualified identity includes package/module and, where selected by policy, scope;
- renames require an explicit catalog alias/migration record;
- a line number or traversal counter is never part of persistent identity;
- hash collision is checked at build time.

Suggested ID generation:

```text
canonical_key = package + "::" + module + "::" + explicit_name
MessageId = stable_hash_64_or_128(canonical_key, fixed_algorithm_version)
```

A 64-bit ID is compact, but a 128-bit ID nearly eliminates accidental collision concerns. A practical catalog may store a 64-bit primary hash plus collision verification string/fingerprint. The hash algorithm and version are part of the catalog format; do not use process-randomized hash maps for persisted IDs.

### 8.3 Extraction policy

Authoritative extraction walks the compiler AST and records only explicit i18n constructs by default.

Heuristic ordinary-string discovery remains useful as a lint:

```text
simple i18n audit-unmarked
```

It may report likely user-visible strings, but it must not generate persistent auto IDs from traversal counters. This prevents false positives for SQL, paths, tests, protocol values, logging keys, code fragments, and generated text.

The Simple CLI application must call the compiler extraction API. Delete the independent line scanner after compatibility tests prove output migration.

### 8.4 Message schema

Each extracted message carries a typed schema:

```simple
struct MessageSchema:
    id: MessageId
    key: AsciiText
    default_locale: LocaleId
    arguments: [MessageArgument]
    source: SourceLocation
    default_ir: MessageIR

struct MessageArgument:
    name: AsciiText
    type: MessageArgType
    required: bool
    formatter: Option<FormatterSpec>
```

Argument types initially include:

- text/text view;
- signed/unsigned integer;
- decimal/float;
- date/time/duration;
- boolean or select symbol;
- enum/symbol with declared variants;
- custom value implementing a safe localized-format trait.

Every locale message is compiled against the same schema. Errors include:

- missing required placeholder;
- undeclared placeholder;
- incompatible formatter/type;
- selector with no fallback;
- unreachable/duplicate variant;
- invalid plural category for the locale only as a warning where exact portability permits broader categories;
- recursive message/term cycle;
- output-bound violation in noalloc profile.

### 8.5 Message IR

Do not perform runtime textual replacement. Compile each message to a compact validated program:

```text
TEXT(offset, byte_len)
ARG(argument_index)
FORMAT(argument_index, formatter_id, option_range)
SELECT(argument_index, variant_table, fallback)
PLURAL(argument_index, plural_rule_id, exact_table, category_table, fallback)
CALL_MESSAGE(message_id, argument_map)
BEGIN_ISOLATE / END_ISOLATE
END
```

Literal text lives in a validated UTF-8 blob. Instructions and tables use compact fixed-width or variable-length encoding chosen by benchmark. The formatter interprets one pass and writes directly to `TextSink`.

Benefits:

- O(message bytes + selected formatting output), not O(arguments × message bytes);
- no accidental replacement of text that resembles a placeholder;
- placeholder typing is resolved before runtime;
- catalog corruption can be validated once at load;
- noalloc formatting is possible;
- single-locale builds can compile the IR into static arrays or direct generated code.

### 8.6 Catalog source and interchange

There are two good layers:

1. **Simple-facing source/catalog files:** preserve `__init__.spl` and `__init__.{locale}.spl` for simple values and generated workflows.
2. **Canonical generated catalog IR:** an SDN or compact binary representation containing IDs, schemas, messages, source maps, and version metadata.

For advanced plural/select syntax, two implementation options exist.

#### Option A — structured catalog declarations first (recommended first phase)

Keep ordinary Simple source grammar unchanged and generate/edit a structured catalog representation:

```simple
# Illustrative generated/editable catalog DSL, not final grammar.
message Files_ (count: i64):
    plural count:
        one: "{count} file"
        other: "{count} files"
```

The catalog compiler parses this only in the i18n toolchain. The general source lexer does not gain the full message grammar.

#### Option B — native message declaration later

After the IR and tooling are stable, Simple may add a declaration form for reusable messages. It should lower to the same schema/IR and remain an optional grammar module if Simple’s configuration-driven/dynload architecture supports that.

**Recommendation:** implement Option A first. It minimizes compiler hot-path change and allows alignment with Unicode MessageFormat and Fluent concepts before freezing a language grammar.

### 8.7 Plural and select behavior

Use CLDR cardinal and ordinal plural rules. A selector supports:

- exact numeric keys such as `=0`;
- CLDR categories;
- string/enum variants;
- mandatory fallback (`other` or explicitly marked default).

Selection is based on the locale and formatter semantics. Do not hard-code English singular/plural branching in application code.

A source/default message may be simple while another locale adds selection. This asymmetric localization principle is valuable and should be supported by the catalog schema: the argument schema must declare available inputs even if the default text does not need every grammatical distinction.

Example:

```simple
# Application source declares stable key and argument schema through use.
val message = Files_"{count} files"(count: file_count)
```

A Korean locale may use one form, while an Arabic locale uses several plural categories. Application code remains unchanged.

### 8.8 Locale context

```simple
struct LocaleContext:
    requested: [LocaleId]
    resolved: LocaleId
    fallback_chain: [LocaleId]
    catalog: MessageCatalog
    formatters: LocaleFormatters
    bidi_policy: BidiIsolationPolicy
```

Core formatting accepts an explicit context:

```simple
fn format_message(
    locale: &LocaleContext,
    id: MessageId,
    args: MessageArgs,
    out: TextSink
) -> Result<(), MessageError>
```

An application framework may bind a context to an actor/task/request and expose a convenience `tr(...)` call. The underlying API remains explicit, which is necessary for servers handling concurrent users with different locales and for deterministic tests.

A thread-local current locale may remain temporarily as a compatibility façade, but compiler/runtime code should not depend on it.

### 8.9 Locale fallback

Use parsed BCP 47 identifiers and a deterministic, configurable fallback chain. A simple starting chain is:

```text
ko-KR -> ko -> project default
zh-Hant-HK -> zh-Hant -> zh -> project default
```

CLDR likely-subtag and parent-locale data may refine negotiation. Requested locale matching and per-message fallback are separate concerns:

1. negotiate the best loaded locale bundle;
2. for a missing message, follow that catalog’s declared parent/fallback chain;
3. fall back to the compiled default message;
4. in development, optionally emit a visible placeholder and diagnostic;
5. in production, never expose internal key text unless policy requests it.

### 8.10 Bidi isolation

Translated text may combine right-to-left message content with left-to-right names, numbers, paths, or identifiers. The message formatter should support automatic FSI/PDI isolation around external substitutions, following the broad strategy used by Fluent and reflected in modern MessageFormat work.

Policy:

- enabled by default for user-facing localized messages;
- formatter knows whether an argument is literal catalog text or external substitution;
- trusted markup and rich-text arguments use a separately typed API;
- logs, protocol output, and machine-readable formats do not use automatic display isolation;
- bidi controls in source/catalogs receive diagnostics under UTS #39/UAX #9 policy.

### 8.11 Formatting values

Avoid locale-sensitive formatting through arbitrary string patterns embedded in application source. Use typed formatter/skeleton specifications where possible:

```simple
Welcome_"Hello, {name}!"(name: user.name)
Balance_"Balance: {amount}"(amount: money.with_style(Currency))
Updated_"Updated {time}"(time: timestamp.with_style(DateTimeShort))
```

The exact surface can evolve, but the schema should store semantic styles rather than locale-specific punctuation patterns. CLDR/ICU guidance favors styles and skeletons because translators should not need to maintain fragile date/number pattern syntax.

Custom formatters implement a bounded, reviewable trait and write to a sink. Mission-critical/noalloc mode requires a declared maximum output or an application-provided buffer.

### 8.12 Catalog layouts by deployment profile

| Profile | Catalog strategy | Lookup | Allocation |
|---|---|---|---|
| Single locale / release | Generated sorted table, perfect hash, or direct switch | O(1) or O(log n), static | None after init |
| Multi-locale desktop/server | Memory-mapped binary catalog with ID index | O(1)/O(log n), borrowed data | Load-time mapping; builder output |
| Hot-reload development | Validated mutable overlay over immutable base | Hash/index overlay | Development-only |
| Embedded/noalloc | Static UTF-8 blob + offset table + message bytecode | O(1)/binary search | None; fixed output buffer |
| Tiny/no-i18n | Localized expressions resolve to defaults at compile time | No runtime catalog | None; i18n module dead-stripped |

The current nested string `HashMap` registry is acceptable as a prototype/development oracle but should not define production architecture.

### 8.13 Compile-time and link-time optimization

- A build with one fixed locale can resolve `MessageId` to one message body at link time.
- Unused messages/locales can be removed by reachability analysis.
- Default-only builds can lower non-parameterized messages to literal `text` constants.
- Parameterized default messages still use compiled IR/builders, not generic locale maps.
- Catalog chunks may be dynloaded for desktop/server language packs.
- The base runtime exposes a narrow `MessageCatalogProvider` interface; advanced i18n is absent if no provider is linked.

### 8.14 Translation tooling

Commands:

```text
simple i18n extract
simple i18n update <locale>
simple i18n check
simple i18n compile
simple i18n audit-unmarked
simple i18n stats
simple i18n pseudo --accented
simple i18n pseudo --rtl
```

Required behaviors:

- preserve translator edits and comments during update;
- mark added/changed/obsolete entries;
- compare placeholder schemas across locales;
- show source locations and defaults;
- deterministic ordering and output;
- pseudolocalization for expansion, combining marks, long words, mirrored/RTL layout, and placeholder isolation;
- catalog format conversion/import/export adapters;
- machine-readable diagnostics for IDE/CI;
- no regex/line scanner as the source of truth.

### 8.15 i18n tests

At minimum:

- simple named lookup and default fallback;
- missing locale and missing message;
- placeholder reorder;
- repeated and omitted placeholders;
- plural categories for representative locales;
- exact numeric match precedence;
- cardinal versus ordinal;
- nested select/plural;
- Korean, Arabic, Russian, Polish, Welsh, and Japanese examples;
- bidi substitutions and isolation;
- emoji/combining text in literals and arguments;
- catalog corruption/version mismatch;
- stable IDs across line movement and unrelated edits;
- rename alias/migration;
- single-locale dead stripping;
- noalloc capacity failure without partial invalid output;
- interpreter, compiler, native, and generated-code parity.

---

## 9. Maintain reference and optimized algorithms together

The user requested separation between fixes and i18n-capable algorithms while maintaining both. The strongest design is a three-tier implementation model.

### 9.1 Tier 0: specification/reference

Portable, readable scalar algorithms define semantics:

- UTF-8 validation/decode/encode;
- UTF-16/32 conversion;
- legacy decoder state machines;
- normalization;
- segmentation;
- case mapping;
- message selection/formatting;
- byte/scalar coordinate conversion.

Reference code favors auditability and exact error behavior. It is always available in tests and in tiny/unsupported-architecture builds.

### 9.2 Tier 1: optimized portable

Algorithmic improvements without architecture intrinsics:

- builders and run copying;
- sparse indexes;
- branch-reduced lookup tables;
- generated compact Unicode tables;
- borrowed slices;
- ASCII quick checks;
- one-pass message IR;
- chunked streaming conversion.

This tier should already avoid O(n²) behavior and excessive allocation.

### 9.3 Tier 2: architecture kernels

SIMD/intrinsic/assembly paths:

- full UTF-8 validation/counting;
- direct transcoding;
- delimiter/structural scans;
- ASCII transforms/search/equality;
- selected property quick checks.

### 9.4 One semantic contract

Every optimized function is compared to the reference on:

- generated valid inputs;
- malformed inputs at every byte position;
- chunk partitions at every boundary for short inputs;
- random chunk partitions for large inputs;
- all supported output-capacity cutoffs;
- all CPU backends;
- sanitizers and fuzzers.

A backend matrix is generated in CI:

| Operation | Scalar | SSE/AVX2 | AVX-512 | NEON | RISC-V V | Tiny |
|---|---|---|---|---|---|---|
| UTF-8 validate | required | parity | parity | parity | planned/parity | scalar |
| UTF-8 count | required | parity | parity | parity | planned/parity | scalar |
| UTF-16→UTF-8 | required | parity | parity | parity | planned | scalar |
| Latin-1→UTF-8 | required | parity | parity | parity | planned | scalar |
| structural scan | required | parity | parity | parity | planned | scalar |

“Complete” means parity tests, performance evidence, and active dispatch—not merely a symbol with an architecture-specific name.

### 9.5 Preventing divergence

- one public API and error model;
- generated shared test vectors;
- scalar code remains executable, not documentation pseudocode;
- architecture functions return the same progress/error structure;
- table generator is shared;
- no copied i18n/string scanners;
- documentation status is generated from test/dispatch inventory;
- a new Unicode/CLDR version updates data and golden results through one controlled process.

---

## 10. Performance methodology and merge gates

### 10.1 Baseline requirement

Before changing code, record the pinned commit baseline for:

- compiler/interpreter/runtime variants;
- x86-64 AVX2 and scalar-forced runs;
- AArch64 NEON and scalar-forced runs;
- RISC-V scalar/QEMU where applicable;
- GC/no-GC, sync/async, mutable/immutable profiles relevant to the library layout;
- tiny/noalloc build.

Store raw results with machine metadata, commit, compiler flags, CPU governor, temperature/frequency conditions, Unicode/CLDR versions, and corpus hashes.

### 10.2 Benchmark harness corrections

- use a monotonic high-resolution clock; do not synthesize nanoseconds from microseconds;
- build corpora before timing with a builder or loaded file;
- measure setup/build separately from operation throughput;
- consume results with a black-box/checksum to prevent elimination;
- warm instruction/data caches separately from cold-start tests;
- run enough samples for confidence intervals; report median and tail;
- pin or record CPU frequency and core affinity;
- report bytes processed, not only iteration count;
- count allocations and allocated bytes;
- use hardware counters where supported;
- compare scalar-forced and auto-dispatch paths;
- make corpus generation deterministic.

### 10.3 Corpus matrix

#### Content families

1. ASCII source/code/log text.
2. Latin-1-style Western text with combining and precomposed forms.
3. Korean Hangul syllables, decomposed Jamo, mixed Korean/ASCII.
4. Japanese kana/kanji and Shift_JIS input.
5. Simplified/traditional Chinese and GB18030/Big5 input.
6. Arabic/Hebrew and bidi controls.
7. Devanagari and combining sequences.
8. emoji, variation selectors, skin tones, flags, keycaps, and ZWJ sequences.
9. mixed multilingual source and messages.
10. adversarial alternating one-/four-byte scalars.
11. malformed UTF-8/16/32 at every structural class.
12. long combining sequences and grapheme stress.
13. real Simple repository source/docs/catalogs.

#### Sizes

```text
0, 1, 2, 3, 4, 7, 8, 15, 16, 23, 31, 32, 63, 64,
127, 128, 255, 256, 1 KiB, 4 KiB, 64 KiB, 1 MiB, 64 MiB
```

Boundary sizes expose scalar/SIMD thresholds, SSO candidates, cache effects, and chunk-state bugs.

### 10.4 Operations

| Group | Benchmarks |
|---|---|
| Primitive | allocation, clone/reference, byte length, scalar length first/cached, ASCII check |
| Validation | valid ASCII/mixed, invalid early/middle/late, first-error offset |
| Traversal | bytes, scalars, reverse scalars, scalar indices, graphemes |
| Index | sequential movement, random scalar ordinal, sparse build, memory overhead |
| Slice/search | boundary checks, substring search, split, trim, line scan |
| Construction | builder append, join, escape JSON, interpolation, normalization output |
| Transcode | all supported pairs/directions, strict/lossy, chunked, short/large |
| I/O | read whole, streaming, line read, async, mapped UTF-8 adopt |
| Parser | lexer and parser by source family; string/f-string/i18n stress |
| Unicode | NFC quick check/normalize, case fold, grapheme segmentation |
| i18n | lookup, default/fallback, plural/select, argument formatting, noalloc |
| System | full compiler wall time, peak RSS, binary size, startup |

### 10.5 Metrics

- ns/op and operations/s for small values;
- GB/s or GiB/s for scans/transcodes;
- cycles/byte and instructions/byte;
- branches and branch misses;
- cache misses where stable;
- allocation count and bytes;
- peak and steady RSS;
- index bytes per source byte/scalar;
- binary and linked-section size by capability;
- compile wall time and frontend percentage;
- startup time and locale/catalog load time.

### 10.5.1 Memory-performance gates

Memory performance is a release gate, not a secondary observation. Every representative benchmark records both execution time and memory behavior. Measurements must separate retained storage from transient workspace and report:

- allocations per operation and allocated bytes per input byte;
- peak transient bytes during decoding, parsing, normalization, indexing, and message formatting;
- steady-state and peak RSS for compiler, runtime, and catalog-loading workloads;
- builder capacity, growth count, and unused reserved capacity;
- sparse/full index bytes per source byte and per scalar;
- Unicode-table and locale-catalog mapped, resident, and linked bytes by capability profile;
- bytes copied per input byte, including intermediate buffers;
- fragmentation or allocator high-water effects for repeated small-string workloads;
- fixed-buffer capacity failures and high-water usage in no-allocation profiles.

Initial memory gates, calibrated against the trustworthy pinned baseline, are:

| Area | Preferred gate | Hard review trigger |
|---|---:|---:|
| UTF transcoding | one output allocation or bounded sink; no scalar-array intermediate | any O(number of scalars) intermediate allocation |
| Lexer/parser hot path | allocation and bytes allocated do not regress | >2% peak RSS or allocated-byte regression |
| Plain `text` traversal | zero side-index allocation | any implicit index allocation |
| Sparse indexing | memory proportional to checkpoints, not scalar count | exceeds documented bytes/source-byte target |
| i18n-disabled/tiny build | no Unicode/i18n data retained or linked beyond selected core | any unexplained resident or binary-data increase |
| Catalog formatting | bounded workspace and direct sink output | temporary message-sized copies or per-argument whole-message copies |
| Noalloc profile | zero heap allocation after initialization | any heap allocation or malformed partial output |

A latency improvement does not pass when it causes an unapproved memory regression. Conversely, a memory reduction that materially slows an ASCII or small-string hot path requires the same documented tradeoff review as any other performance regression.

### 10.6 Initial regression gates

These are **proposed gates to calibrate after the first trustworthy baseline**, not measured claims.

| Area | Preferred gate | Hard review trigger |
|---|---:|---:|
| ASCII compiler wall time | no regression; target improvement | >1% median regression |
| ASCII lex-only throughput | no regression; target improvement | >2% regression |
| Existing byte/search APIs | no regression | >2% regression on representative sizes |
| Small string operations | no material regression | >2% or one extra allocation in hot operation |
| Full compiler peak RSS | no regression | >2% without documented tradeoff |
| Base/tiny binary size | capability-neutral | any unexplained Unicode/i18n linkage |
| UTF-8 validation | improve or match scalar baseline | slower than old auto-dispatch on representative corpora |
| UTF-16/Latin-1 conversion | remove intermediate allocation | any code-point-array allocation in production path |
| Repeated scalar ordinal access | bounded improvement with index | sparse index fails memory/latency target |
| i18n-disabled runtime | zero catalog lookup cost | registry/data linked or branch in ordinary literal path |

A regression may be accepted only with a documented correctness requirement and compensating profile/fast path. Aggregate averages cannot hide severe small-string or ASCII regressions.

### 10.7 Performance result storage

Add machine-readable records, for example:

```text
doc/10_metrics/text_i18n/
    baseline_112ac203_<machine>.json
    result_<commit>_<machine>.json
    corpus_manifest.sdn
    report_<commit>.md
```

CI compares matched machines/configurations and flags statistically meaningful changes. A benchmark command emits human, JSON, and CI summary modes.

---
## 11. File-level implementation plan

### 11.1 Workstream map

| Workstream | Main responsibility | Must land before |
|---|---|---|
| W0 Measurement | Trustworthy baseline, corpus, backend inventory | All performance claims |
| W1 Invariants | Valid UTF-8 `text`, explicit byte/scalar APIs, correctness fixes | Unicode/i18n expansion |
| W2 Builders and views | `TextSlice`, `TextIndex`, cursor, builder, fixed buffer | Parser/i18n formatting optimization |
| W3 Codecs and I/O | Streaming decoders/encoders, typed text readers/writers | Legacy encoding support |
| W4 Parser | Byte/block scanner, borrowed tokens, unified string/i18n scan | Frontend performance gate |
| W5 Unicode data | UAX #15/#29/#31/#39, generated versioned tables | Full Unicode language/UI behavior |
| W6 i18n | Typed extraction, catalog IR, locale context, plural/select | Production localization |
| W7 SIMD | Complete kernels and centralized dispatch | Final performance targets |
| W8 Migration/docs | Lints, compatibility façade, doc/spec status repair | Stable release |

### 11.2 Phase 0 — baseline and semantic lock

**Deliverables**

- record repository snapshot and current ABI;
- enumerate every public/internal string constructor and whether it validates;
- classify every `len`, slice, index, char, width, and bytes-to-text use;
- build corpora and corrected benchmark harness;
- force scalar and each SIMD backend independently;
- add golden malformed-encoding vectors;
- create an ADR locking byte/scalar/grapheme/display definitions;
- update the SIMD completion document to “audit required” until backend parity is proven.

**Likely files**

```text
src/lib/*/benchmark/string_bench.spl
src/compiler_rust/**/benches or existing benchmark framework
test/03_system/text_i18n/**
doc/02_requirements/lib/text_i18n/**
doc/04_architecture/lib/text_i18n/**
doc/10_metrics/text_i18n/**
```

**Exit criteria**

- reproducible baseline JSON exists;
- scalar/reference results are available;
- the public semantic table is reviewed;
- no implementation PR can claim improvement without the baseline.

### 11.3 Phase 1 — invariant and correctness fixes

#### `src/lib/common/string_core.spl`

- add `byte_at`, explicit byte slicing, UTF-8-boundary checks;
- make `str_char_at` compatibility-only and deprecate it;
- implement scalar-returning access through `UnicodeScalar`;
- rename ASCII-only helpers;
- replace unchecked public byte-to-text conversion;
- add tests for every 1–4-byte scalar and continuation-byte boundary.

#### `src/lib/common/encoding/utf8.spl`

- define normative scalar decoder/error behavior;
- add boundary predicates, next/previous index, scalar iterator primitives;
- ensure malformed lead-byte classification is exact;
- expose validation proof only internally;
- preserve ASCII/count caching.

#### `src/lib/common/encoding/codec.spl`

- remove unknown-to-UTF-8 fallback;
- fix replacement to operate on decoded errors/scalars;
- route production conversion to streaming decoder/encoder;
- retain code-point-array path temporarily as test/reference only;
- mark exact versus WHATWG codec labels.

#### `src/lib/common/encoding/text_ops.spl` and `char_mode.spl`

- add explicit byte/scalar/grapheme functions;
- freeze global mode as deprecated compatibility API;
- migrate callers before removal;
- prevent one-byte malformed `text` return.

#### Runtime constructors

- validate all external byte ingress;
- add internal trusted constructor with proof;
- verify NUL/length semantics across C/Rust/Simple;
- audit FFI pointer-only calls.

**Exit criteria**

- public safe code cannot create malformed `text`;
- every ambiguous API has explicit replacement and lint/deprecation path;
- all current tests plus new malformed/boundary tests pass;
- baseline ASCII performance is within the hard gate.

### 11.4 Phase 2 — views, cursor, builder, and fixed-capacity text

**New/updated modules**

```text
src/lib/common/text/view.spl
src/lib/common/text/index.spl
src/lib/common/text/cursor.spl
src/lib/common/text/builder.spl
src/lib/common/text/fixed.spl
src/runtime/runtime_string_builder.*
```

**Tasks**

- implement `TextView`/`TextSlice` without changing primitive storage;
- implement `TextIndex` and forward/backward scalar movement;
- implement scalar iterators yielding native indexes;
- implement growable and fixed-capacity `TextSink`/builder;
- replace recursive batch joins in hot library paths;
- add `Utf8Buf<N>`, `Ascii<N>`, and `Bytes<N>`;
- define mutation/index invalidation semantics;
- benchmark compiler, formatter, JSON escaping, splitting, and joining.

**Exit criteria**

- no O(n²) character-by-character builder patterns remain in designated hot paths;
- fixed buffer never exposes malformed partial output;
- borrowed slice behavior is proven by lifetime/owner tests;
- no base `text` ABI change.

### 11.5 Phase 3 — streaming codec and I/O redesign

**New/updated modules**

```text
src/lib/common/encoding/decoder.spl
src/lib/common/encoding/encoder.spl
src/lib/common/encoding/utf16.spl
src/lib/common/encoding/utf32.spl
src/lib/common/encoding/latin1.spl
src/lib/common/encoding/legacy/**
src/lib/common/io/traits.spl
src/lib/common/io/text_reader.spl
src/lib/common/io/text_writer.spl
```

**Tasks**

- narrow `Read`/`Write` to bytes;
- implement stateful UTF decoders and direct output;
- support every chunk split for short test vectors;
- add exact `Latin1` and `Windows1252` distinction;
- implement output preflight and bounded-sink progress;
- add UTF-8 adopt/borrow fast path;
- add legacy codecs in priority order based on product needs: CP949/EUC-KR compatibility, Shift_JIS, GB18030, Big5;
- use pinned mapping generators and differential oracles;
- add async adapters using the same decoder state.

**Exit criteria**

- production conversions allocate no integer code-point array;
- strict errors report absolute byte offset;
- all chunk partitions match whole-buffer decoding;
- I/O defaults to strict UTF-8;
- unknown encoding is a typed error;
- before/after throughput and allocation report is attached.

### 11.6 Phase 4 — parser/frontend optimization

**Files**

```text
src/compiler_rust/parser/src/lexer/mod.rs
src/compiler_rust/parser/src/lexer/strings.rs
src/compiler_rust/parser/src/lexer/i18n.rs
src/compiler_rust/parser/src/lexer/identifiers.rs
src/compiler_rust/parser/src/token.rs
src/compiler_rust/parser/src/source_map/** (new or existing equivalent)
```

**Tasks**

- replace scalar iterator core with byte cursor over valid UTF-8;
- add block special-byte scanning through the common kernel API;
- borrow token spans when no decoding is needed;
- unify ordinary/raw/triple/f/i18n scanner;
- parse interpolation from source spans;
- remove large lexer/string clones from backtracking;
- fix suffix byte/scalar mismatch;
- implement line-start source map and lazy UTF-16 columns;
- implement ASCII identifier fast path and UAX #31 slow path;
- preserve exact original spelling for diagnostics while interning NFC identity;
- compare frontend output/diagnostics byte-for-byte where semantics are unchanged.

**Exit criteria**

- ASCII lexing meets gate;
- multilingual source has correct spans and diagnostics;
- LSP position conversions pass UTF-8/UTF-16 tests;
- ordinary and i18n literals share scanner/escape tests;
- parser memory allocation decreases or is justified.

### 11.7 Phase 5 — sparse indexing and large-text providers

**Tasks**

- replace global handle map with owner-bound `IndexedText`;
- implement sparse checkpoint backend;
- benchmark strides and adaptive threshold;
- add full-table backend only for comparison/explicit opt-in;
- prototype continuation bitmap/rank-select for very large random-access workloads;
- add `TextProvider`/`UText`-like abstraction for rope/mapped/chunked text where needed;
- implement rope metrics in editor/document library, not base runtime.

**Exit criteria**

- repeated ordinal access improves without excessive memory;
- index lifetime is automatic;
- ASCII path does not allocate an index;
- current `rt_swi_*` compatibility calls route to the new owner-safe implementation or are removed;
- algorithm names accurately describe representation.

### 11.8 Phase 6 — Unicode data and language semantics

**Tasks**

- add pinned Unicode data generator;
- implement NFC/NFD first, then NFKC/NFKD;
- implement UAX #29 extended grapheme segmentation;
- implement XID identifier tables and NFC symbol identity;
- add case fold and default case mappings;
- add locale-sensitive case specializations where required;
- add UTS #39 diagnostics;
- move terminal width to policy-based terminal module;
- expose Unicode version and data hashes;
- fuzz against ICU or another mature oracle.

**Exit criteria**

- normalization conformance tests pass;
- grapheme break tests pass;
- identifier tests pass for Unicode 17;
- generated tables are capability-split and reproducible;
- base/tiny binary does not link unused data.

### 11.9 Phase 7 — production i18n

**Files**

```text
src/compiler_rust/compiler/src/i18n/extractor.rs
src/compiler_rust/compiler/src/i18n/locale.rs
src/compiler_rust/compiler/src/i18n/registry.rs
src/compiler_rust/compiler/src/i18n/message_ir.rs        # new
src/compiler_rust/compiler/src/i18n/catalog.rs           # new
src/compiler_rust/compiler/src/i18n/schema.rs            # new
src/compiler_rust/compiler/src/interpreter/expr/literals.rs
src/app/i18n/main.spl
src/lib/common/i18n/**
```

**Tasks**

- make AST extractor the sole authority;
- separate `audit-unmarked` from extraction;
- define stable MessageId/versioned hash;
- compile defaults and translations to typed MessageIR;
- add schema validation across locales;
- implement explicit `LocaleContext`;
- replace repeated `String.replace` with one-pass sink formatting;
- implement CLDR plural/select;
- add bidi-isolation policy;
- generate static/perfect-hash and mapped catalogs;
- implement single-locale/default-only optimization;
- implement noalloc catalog/output profile;
- preserve/update `__init__.{locale}.spl` workflow;
- add pseudolocalization and migration tooling.

**Exit criteria**

- all current syntax remains valid;
- locale output is UTF-8 `text`;
- placeholders are compile-time checked;
- concurrent locales do not depend on global mutable state;
- i18n-disabled builds have no linked registry/data and no ordinary-string hot-path branch;
- catalog and formatter benchmarks meet gates.

### 11.10 Phase 8 — full SIMD and backend closure

**Tasks**

- implement/integrate full-block UTF-8 validation rather than ASCII-prefix-only wrappers;
- add direct UTF-16/32/Latin-1 conversion kernels;
- add parser structural scan kernels;
- centralize runtime dispatch and thresholds;
- add forced-backend CI;
- generate implementation-status documentation from dispatch/tests;
- validate RISC-V V path when hardware/toolchain is available;
- keep scalar tiny profile.

**Exit criteria**

- every claimed backend operation has parity and benchmark evidence;
- no duplicate internal CPU dispatch systems;
- short inputs route to measured scalar path;
- unsupported CPUs use correct scalar code;
- status documents match executable inventory.

### 11.11 Phase 9 — migration and removal

- migrate all internal ambiguous `.len()`/indexing uses;
- turn warnings into errors in new language edition or mission-critical profile;
- remove global char mode from core;
- remove independent line-based i18n extractor;
- remove unchecked public byte-to-text API;
- remove/manual-free global string-index handles;
- archive superseded design claims with links to the new ADR;
- publish porting guide and automated fix suggestions.

---

## 12. Migration strategy

### 12.1 Compatibility stages

#### Stage A — explicit alternatives, no semantic break

- add `byte_len`, `scalar_len`, `byte_at`, `scalar_at`, cursors, checked slices;
- existing `len`, `[]`, and legacy char APIs retain behavior;
- compiler emits optional audit warnings;
- runtime validates new public byte ingress.

#### Stage B — warnings in Unicode-sensitive contexts

Warn for patterns such as:

```simple
for i in 0..s.len():
    use(s[i])
```

when `s` is `text`, and suggest:

```simple
for c in s.scalars():
    use(c)
```

or:

```simple
for b in s.bytes():
    use(b)
```

Warn when a one-byte slice is returned as `text`, when UI width uses byte/scalar length, and when unchecked bytes become text.

#### Stage C — new-edition strictness

A future Simple language edition can disallow ambiguous integer indexing on `text` and require explicit units. Existing edition code continues under compatibility mode. Mission-critical mode may adopt strictness early.

### 12.2 Automated migration

Compiler/lint fixes should offer:

- `s.len()` → `s.byte_len()` when used for buffers, slices, I/O, hashes, or byte spans;
- index loops → `.bytes()`, `.scalars()`, or `.scalar_indices()` based on operations;
- `s[i:i+1]` → byte slice or `TextCursor` scalar slice;
- `rt_bytes_to_text` → strict/lossy/unsafe constructor according to surrounding error path;
- global char mode calls → explicit operation variants;
- repeated concatenation → builder pattern;
- thread-local locale calls → explicit context parameter where feasible.

Automatic fixes must be conservative. When unit intent cannot be proven, the lint presents alternatives instead of guessing.

### 12.3 API naming rules

- APIs containing `byte` operate in bytes and return byte offsets/ranges.
- APIs containing `scalar` operate in Unicode scalar values/ordinals.
- APIs containing `grapheme` follow pinned UAX #29.
- APIs containing `utf16` expose UTF-16 code-unit positions for interoperability.
- APIs containing `display` require a width/layout policy.
- `char` is reserved for a precisely defined scalar type only if the language chooses that alias; otherwise avoid it in public string APIs.
- `encoding` names external byte representation; it is not an indexing mode.

---

## 13. Parallel implementation plan

The work is parallelizable after the semantic lock and baseline. Use parent-authoritative integration: the parent workstream owns the architectural contracts and integration branch; agents consume immutable snapshots and return isolated commits/results. Shared files with high conflict risk require explicit ownership windows.

### 13.1 Agent/work package table

| Agent | Scope | Primary outputs | Dependencies | Must not change independently |
|---|---|---|---|---|
| A0 Architecture/integration | ADR, type/API contracts, merge ordering | Semantic spec, integration tests, conflict resolution | none | Backend algorithms without owner review |
| A1 Audit/benchmark | inventory, corpora, harness, baseline | JSON results, gates, profiler reports | snapshot | Public semantics |
| A2 UTF-8 correctness | validators, constructors, boundaries, scalar oracle | Reference kernels and tests | A0 | i18n/catalog grammar |
| A3 Builder/view/fixed | slices, cursor, builder, `Utf8Buf<N>` | Runtime/std-lib implementation | A0/A2 | Parser token model without A4 coordination |
| A4 Parser/frontend | byte scanner, source map, borrowed tokens | Lexer/parser refactor and benchmarks | A0/A1/A2/A3 interfaces | Unicode table format |
| A5 Codecs/I/O | streaming decoder/encoder, text reader/writer | UTF/Latin/legacy codecs and tests | A0/A2/A3 | Core string ABI |
| A6 SIMD | complete native kernels/dispatch | x86/ARM/RISC-V implementations | A1/A2/A5 contracts | Error semantics |
| A7 Unicode data | generators, normalization, segmentation, XID/security | Versioned tables and conformance tests | A0/A2 | Parser grammar |
| A8 i18n compiler | extractor, schema, MessageIR/catalog compiler | Rust compiler/tooling implementation | A0/A3/A7 plural data | Base text representation |
| A9 i18n runtime | locale context, catalog lookup, formatter/noalloc | Runtime/std-lib implementation | A3/A7/A8 IR | Source extraction rules |
| A10 Migration/docs | lints, fixers, porting guide, status generation | diagnostics and docs | all contracts | Semantics before A0 approval |
| A11 Fuzz/security | fuzz matrices, confusables/bidi/adversarial inputs | Reproducers, differential evidence | A2/A5/A7/A8 | Production code except minimal repro fixes |

### 13.2 Merge order

1. A0 semantic ADR and A1 baseline.
2. A2 invariant/reference fixes.
3. A3 builder/view/fixed foundations.
4. A5 streaming UTF codecs and byte/text I/O split.
5. A4 parser refactor using A3/A2 APIs.
6. A7 Unicode generated data and semantics.
7. A8/A9 i18n schema/catalog/runtime.
8. A6 optimized SIMD kernels can develop in parallel after contracts, but dispatch lands after reference tests.
9. A10 migration and documentation closure.
10. A11 fuzz/security runs continuously and gates each merge wave.

### 13.3 Agent acceptance packet

Every agent result includes:

- changed file list;
- semantic assumptions;
- tests added and commands;
- scalar/reference parity evidence;
- before/after performance data where relevant;
- allocations/memory/binary-size effects;
- unsupported cases and next dependencies;
- conflict notes for shared files;
- no speculative “complete” status without evidence.

### 13.4 Shared-file coordination

High-conflict files:

```text
src/lib/common/string_core.spl
src/lib/common/encoding/utf8.spl
src/compiler_rust/parser/src/lexer/mod.rs
src/compiler_rust/compiler/src/interpreter/expr/literals.rs
src/runtime/runtime_simd_dispatch.h
```

The integration owner should split interfaces first or assign serial ownership windows. Agents should not independently rewrite the same large lexer/runtime files and attempt a late merge.

---

## 14. Verification and test design

### 14.1 UTF-8 invariant tests

- every valid scalar boundary and byte length;
- shortest/longest 1–4-byte forms;
- overlong sequences;
- isolated continuation bytes;
- truncated sequence at every length;
- surrogate encodings;
- values above U+10FFFF;
- embedded NUL;
- invalid slice endpoints;
- reverse traversal at all boundaries;
- cache correctness after clone/intern/build;
- no malformed `text` returned by safe APIs.

Use Unicode’s official UTF-8 test data where applicable and generated exhaustive short-byte tests.

### 14.2 Streaming partition tests

For every short encoded input, test every possible partition into chunks, including empty chunks and output capacities from zero through full length. Whole-buffer and streaming results must match exactly in output, progress, and first-error offset.

### 14.3 Unicode conformance

- NormalizationTest.txt for UAX #15;
- GraphemeBreakTest.txt, WordBreakTest.txt, SentenceBreakTest.txt for UAX #29;
- LineBreakTest.txt if line breaking is implemented;
- DerivedCoreProperties/XID data for identifiers;
- CaseFolding/SpecialCasing data;
- bidi/security-specific tests for diagnostics;
- version-update differential report.

### 14.4 Parser differential tests

Before refactoring, serialize tokens/AST/spans/diagnostics for representative repository files. After refactoring, compare:

- token kinds and byte spans;
- literal decoded values;
- interpolation expression spans/AST;
- line and diagnostic positions;
- error recovery;
- i18n extraction;
- source hashes/incremental dependencies.

Intentional Unicode identifier changes are reviewed separately from scanner optimization.

### 14.5 Property-based tests

Properties:

```text
encode_utf8(decode_utf8(valid_bytes)) == valid_bytes
normalize(normalize(s, F), F) == normalize(s, F)
byte_slice(valid_boundaries) is valid UTF-8
cursor next then previous returns same boundary/scalar
sparse_index ordinal conversion == scalar reference scan
stream_decode(all_partitions) == whole_decode
optimized(operation, input) == reference(operation, input)
compiled_message(args) == reference_message_interpreter(args)
```

### 14.6 Fuzz targets

- all public decoders and encoders;
- builder capacity transitions;
- checked/unchecked boundary APIs with proof generation;
- unified string/f-string/i18n lexer;
- Unicode identifiers and normalization;
- catalog parser and binary loader;
- message formatter and selector tables;
- bidi isolation;
- source-map byte/UTF-16 conversion;
- sparse/full/rank-select index backends;
- CPU-dispatch equivalence.

### 14.7 Security tests

- invalid UTF-8 hiding ASCII delimiters;
- replacement-mode delimiter masking;
- path/config canonicalization mistakes;
- mixed-script/confusable identifiers;
- bidi source-control attacks;
- unbalanced isolation controls in catalogs;
- catalog hash collision handling;
- malicious message recursion/depth/output expansion;
- integer overflow in output bounds and index tables;
- huge combining sequences and denial-of-service limits;
- malformed mapped catalog offsets.

### 14.8 Noalloc and mission-critical tests

- no heap call after declared initialization point;
- bounded decoder state;
- bounded builder failure is deterministic and leaves valid prefix/state;
- catalog lookup and formatting use static memory;
- Unicode capability selection is explicit;
- no global mutable locale/char mode;
- all unsafe constructors have proof-producing call paths;
- WCET-relevant loops have documented bounds for fixed input/buffer sizes.

---

## 15. Decision matrix and rejected alternatives

### 15.1 Internal storage alternatives

| Alternative | ASCII memory | Scalar indexing | Grapheme indexing | I/O conversion | ABI/migration | Decision |
|---|---:|---:|---:|---:|---:|---|
| UTF-8 flat text | best | scan/index | segmentation | best for modern I/O | already present | **Adopt** |
| UTF-16 | ~2× ASCII | code-unit, not scalar | segmentation | converts source/web/Unix | high disruption | Reject |
| UTF-32 | ~4× ASCII | O(1) scalar | still segmentation | converts most I/O | very high | Reject |
| PEP 393-style 1/2/4 byte | adaptive | O(1) scalar | still segmentation | cached/conversion complexity | major ABI/branching | Reject for base type |
| Rope for every string | metadata-heavy | tree metric | possible | flatten/conversion | major overhead | Reject as default; adopt for large editors |
| Dual UTF-8/UTF-16 cache | high/variable | mixed | still segmentation | cache invalidation | complex | Reject for immutable base; targeted adapter only |

### 15.2 Indexing alternatives

| Alternative | Strength | Weakness | Decision |
|---|---|---|---|
| Hidden scalar semantics for `text[i]` | superficially convenient | O(n), quadratic loops, ambiguous return unit | Reject |
| One-byte `text[i]` | fast | can create invalid text and mislead users | Deprecate; expose `byte_at` |
| Opaque/native `TextIndex` | O(1) local movement, safe boundaries | not an ordinal | **Adopt** |
| Full scalar-start table by default | O(1) nth access | large memory/build/lock cost | Reject as default; optional explicit backend |
| Sparse checkpoints | bounded scan, low metadata | nth not strict O(1) | **Adopt lazily** |
| Succinct rank/select | excellent theoretical memory/query balance | implementation complexity and constants | Benchmark-gated large-text backend |

### 15.3 Encoding alternatives

| Alternative | Decision | Reason |
|---|---|---|
| Decode through `[i64]` code-point array | Reference/test only | Allocation and memory traffic; no streaming |
| Direct streaming source→UTF-8 | **Adopt** | Correct chunking, lower memory, SIMD-compatible |
| Unknown label defaults to UTF-8 | Reject | Silent corruption/security risk |
| Universal heuristic autodetection | Reject from core | Unreliable; separate optional tool |
| Strict default with explicit lossy mode | **Adopt** | Safe and reviewable |
| Platform default encoding | Reject as implicit behavior | Non-deterministic builds/runtime |

### 15.4 i18n alternatives

| Alternative | Decision | Reason |
|---|---|---|
| All strings automatically localizable | Reject | Hot-path overhead, false positives, unstable IDs |
| Preserve explicit `Name_"..."` | **Adopt** | Existing ergonomic marker and compiler knowledge |
| Runtime nested string hash maps for all profiles | Prototype/dev only | Clones, allocations, noalloc incompatibility |
| Compiled typed MessageIR | **Adopt** | Correct placeholders/plurals and one-pass output |
| English-only singular/plural APIs | Reject | Incorrect for many locales |
| Full MessageFormat grammar in ordinary lexer | Reject initially | Parser/hot-path complexity |
| Structured catalog compiler aligned with MessageFormat | **Adopt first** | Interoperability without core grammar cost |
| Global current locale as core contract | Reject | Concurrent requests/tests become implicit |
| Explicit context plus convenience binding | **Adopt** | Composable and optimizable |

### 15.5 SSO

**Benchmark-gated, deferred.** It can be valuable, but changing the primitive representation before fixing construction, interning, views, and fixed buffers would mix a correctness migration with a high-risk ABI migration. The report does not reject SSO permanently; it rejects treating it as the first or required solution.

---

## 16. Risks and mitigations

| Risk | Failure mode | Mitigation |
|---|---|---|
| Silent semantic break | `len`/index meaning changes existing code | Compatibility stage, explicit APIs, edition/lint migration |
| Invalid text remains reachable | Legacy/FFI constructor bypasses validation | Constructor inventory, proof-gated unsafe API, sanitizer/fuzz |
| ASCII slowdown | Unicode checks enter every hot loop | Byte scanner, ASCII flags, capability dead stripping, gates |
| Unicode table bloat | Tiny/compiler builds link full locale data | Generated capability partitions and link-time reachability |
| Duplicate implementations diverge | Simple/Rust/C scanners/codecs disagree | One semantic oracle, shared vectors, route CLI to compiler API |
| SIMD status overclaimed | Architecture wrapper mostly calls scalar | Forced-backend tests and generated status matrix |
| Index memory blowup | Full offsets cached for common strings | Plain iteration default, sparse lazy index, owner-bound lifetime |
| Locale global state bugs | concurrent user/request contamination | explicit `LocaleContext` |
| Catalog format freezes too early | grammar incompatible with standards/tooling | stable internal IR, structured catalog first, syntax ADR later |
| Legacy codec incompatibility | hand-coded mapping differs from deployed behavior | WHATWG/encoding_rs differential oracle and pinned tables |
| Normalization changes identity unexpectedly | user data/path corruption | no automatic normalization except identifier identity profile |
| Grapheme assumptions break | UI treats scalar as user character | dedicated grapheme view and conformance tests |
| Display width remains wrong | terminal/font policies differ | explicit width policy; no universal base-string width |
| Noalloc output truncation | malformed or misleading partial message | transactional append/default capacity error; explicit truncation only |
| Message expansion DoS | nested/select/formatter output unbounded | depth/output limits, schema validation, bounded sink |

---
## 17. Requirements traceability

| User request | Report decision |
|---|---|
| Efficiently convert other encodings to UTF-8 | Direct stateful streaming decoders, no code-point-array production path, strict/lossy modes, SIMD UTF/Latin fast paths, WHATWG-compatible legacy mappings |
| Update string and I/O libraries with before/after checks | Explicit file-level phases plus corrected benchmark harness, corpus, metrics, and merge gates |
| Efficiently parse variable-length international strings | UTF-8-valid source, byte spans/cursor, ASCII block scanning, borrowed slices, Unicode slow path, unified string/i18n scanner |
| Efficient string indexing/movement | Native-boundary `TextIndex` and cursor; sparse `IndexedText` for repeated ordinal access; grapheme view for UI |
| SIMD for parsing and string libraries | Central dispatch, full validation/transcoding, structural masks, scalar thresholds, forced-backend parity |
| Separate fixes and i18n-capable algorithms; maintain both | Tier 0 scalar reference, Tier 1 portable optimization, Tier 2 SIMD; i18n as optional upper layer |
| Simple language i18n | Preserve `Name_"..."`, typed schemas, compiled MessageIR, CLDR plural/select, explicit locale context, static/noalloc profiles |
| Recheck original text architecture | Retain goals but merge into existing primitive `text`; reject duplicate `Text`; defer SSO |
| Variable and fixed length | `text`/builder for dynamic values; `Utf8Buf<N>` measured in bytes; rope for very large editable text |
| Minimize performance loss | No semantic change to hot byte path initially, ASCII quick paths, dead-strippable capabilities, regression gates |
| End-of-document rules | Section 20 is the normative rule set |

---

## 18. Definition of done

The text/i18n program is not complete until all of the following are true:

1. safe public APIs cannot construct malformed `text`;
2. every public index/length API states its coordinate and complexity;
3. byte, scalar, grapheme, UTF-16, and display coordinates have distinct types or unambiguous APIs;
4. production transcoding streams directly to UTF-8 without a code-point array;
5. strict errors and all chunk splits are verified;
6. the lexer uses byte spans and measured ASCII/block fast paths;
7. source identifiers follow the pinned XID/NFC/security profile;
8. scalar, optimized portable, and SIMD implementations have differential parity;
9. the current “SIMD complete” documentation is reconciled with executable backend evidence;
10. the independent Simple i18n line scanner is removed or only delegates to the AST extractor;
11. message placeholder schemas are checked across locales;
12. plural/select behavior uses pinned CLDR data;
13. message formatting is one pass to a sink and does not repeatedly replace strings;
14. locale state is explicit in core APIs;
15. default-only, single-locale, multi-locale, and noalloc profiles are tested;
16. i18n-disabled and tiny builds do not link unused locale/Unicode capabilities;
17. trustworthy before/after benchmark artifacts are committed;
18. allocation rate, transient bytes, peak/steady RSS, index overhead, and linked Unicode/catalog data satisfy the calibrated memory-performance gates;
19. migration lints/fixes and a porting guide exist;
20. Unicode/CLDR version updates are reproducible and conformance-tested;
21. every accepted time or memory regression has a documented correctness/tradeoff record.

---

## 19. Research and standards references

### Unicode and locale standards

- Unicode 17.0.0: <https://www.unicode.org/versions/Unicode17.0.0/>
- UAX #15, Unicode Normalization Forms: <https://www.unicode.org/reports/tr15/>
- UAX #29, Unicode Text Segmentation: <https://www.unicode.org/reports/tr29/>
- UAX #31, Unicode Identifiers and Syntax: <https://www.unicode.org/reports/tr31/>
- UAX #14, Unicode Line Breaking Algorithm: <https://www.unicode.org/reports/tr14/>
- UAX #9, Unicode Bidirectional Algorithm: <https://www.unicode.org/reports/tr9/>
- UTS #39, Unicode Security Mechanisms: <https://www.unicode.org/reports/tr39/>
- CLDR 48 release/update notes, including 48.2.1: <https://cldr.unicode.org/downloads/cldr-48>
- LDML 48.2: <https://www.unicode.org/reports/tr35/tr35-78/tr35.html>
- CLDR plural rules: <https://www.unicode.org/cldr/charts/latest/supplemental/language_plural_rules.html>
- Unicode MessageFormat specification: <https://www.unicode.org/reports/tr35/tr35-76/tr35-messageFormat.html>
- MessageFormat working group: <https://github.com/unicode-org/message-format-wg>

### Encoding and conversion

- WHATWG Encoding Standard: <https://encoding.spec.whatwg.org/>
- ICU converter guide: <https://unicode-org.github.io/icu/userguide/conversion/converters.html>
- ICU UTF-8 guide: <https://unicode-org.github.io/icu/userguide/strings/utf-8.html>
- ICU UText: <https://unicode-org.github.io/icu/userguide/strings/utext.html>
- `encoding_rs`: <https://github.com/hsivonen/encoding_rs>
- `simdutf`: <https://github.com/simdutf/simdutf>
- Keiser and Lemire, *Validating UTF-8 In Less Than One Instruction Per Byte*: <https://arxiv.org/abs/2010.03090>
- Lemire and Muła, *Transcoding Billions of Unicode Characters per Second with SIMD Instructions*: <https://arxiv.org/abs/2109.10433>
- Clausecker and Lemire, *Transcoding Unicode Characters with AVX-512 Instructions*: <https://arxiv.org/abs/2212.05098>

### Parsing and search

- Langdale and Lemire, *Parsing Gigabytes of JSON per Second*: <https://arxiv.org/abs/1902.08318>
- `simdjson`: <https://github.com/simdjson/simdjson>
- Rust `memchr`: <https://github.com/BurntSushi/memchr>
- Tree-sitter parser API: <https://tree-sitter.github.io/tree-sitter/using-parsers/2-basic-parsing.html>

### String representations and indexing

- Rust `str`: <https://doc.rust-lang.org/std/primitive.str.html>
- Rob Pike, *Strings, bytes, runes and characters in Go*: <https://go.dev/blog/strings>
- Swift, *UTF-8 String*: <https://www.swift.org/blog/utf8-string/>
- Python PEP 393: <https://peps.python.org/pep-0393/>
- Julia strings: <https://docs.julialang.org/en/v1/manual/strings/>
- Zig language reference: <https://ziglang.org/documentation/master/>
- Rust `arrayvec::ArrayString`: <https://docs.rs/arrayvec/latest/arrayvec/struct.ArrayString.html>
- Xi Editor rope science, metrics: <https://xi-editor.io/docs/rope_science_02.html>
- Xi Editor rope model: <https://xi-editor.io/docs/rope_science_00.html>
- Raman, Raman, and Rao, succinct indexable dictionaries: <https://dl.acm.org/doi/10.5555/545381.545411>

### Localization systems

- ICU message formatting: <https://unicode-org.github.io/icu/userguide/format_parse/messages/>
- Project Fluent: <https://projectfluent.org/>
- Fluent selectors: <https://projectfluent.org/fluent/guide/selectors.html>
- Fluent specification repository: <https://github.com/projectfluent/fluent>
- Fluent bidi background: <https://github.com/projectfluent/fluent/wiki/BiDi-in-Fluent>

### Audited Simple repository material

All links below are pinned to the audited commit.

- Runtime SIMD/string header: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/runtime/runtime_simd_dispatch.h>
- Runtime core string: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/runtime/simple_core/core_string.spl>
- Common string core: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/string_core.spl>
- Common text helpers: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/text.spl>
- UTF-8 module: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/utf8.spl>
- UTF-16 module: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/utf16.spl>
- Generic codec: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/codec.spl>
- Text operations and character mode: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/text_ops.spl>, <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/char_mode.spl>
- Width/index wrapper: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/encoding/width_index.spl>
- Rust UTF-8 kernels: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/runtime/src/value/utf8_kernels.rs>
- I/O traits: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/common/io/traits.spl>
- Rust lexer: <https://github.com/ormastes/simple/tree/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/parser/src/lexer>
- Rust i18n compiler: <https://github.com/ormastes/simple/tree/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/compiler_rust/compiler/src/i18n>
- Simple i18n CLI: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/app/i18n/main.spl>
- Existing text engine design: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/doc/05_design/lib/text_i18n/text_encoding_engine.md>
- Existing locale init design: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/doc/05_design/lib/text_i18n/i18n_init_locale_spec.md>
- Existing SIMD plan/status: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/doc/03_plan/compiler/simd_opt/simd_utf8_text_api_optimization.md>
- Existing string benchmark: <https://github.com/ormastes/simple/blob/112ac2030f0c5c442c480cb0e86916402e5c5eeb/src/lib/gc_async_mut/benchmark/string_bench.spl>

---

## 20. Final normative rules

These rules are the recommended review and implementation policy for all new Simple text, parser, I/O, Unicode, and i18n code.

1. **`text` MUST contain valid UTF-8.** Malformed bytes are never a safe `text` value.
2. **Arbitrary bytes MUST use a byte type.** `[u8]`, `ByteSlice`, and byte buffers are not implicitly text.
3. **External bytes MUST be decoded at a boundary.** Internal algorithms do not carry an implicit current encoding.
4. **Strict decoding MUST be the default.** Lossy replacement or ignoring errors is explicitly named and observable.
5. **Unknown encodings MUST be errors.** They never fall back silently to UTF-8 or a platform default.
6. **Core APIs MUST NOT heuristically detect encodings.** Detection is an optional separate tool with confidence metadata.
7. **Each length/index/range MUST name its coordinate.** Byte, scalar, grapheme, UTF-16, and display units are not interchangeable integers.
8. **Compiler and parser spans MUST remain UTF-8 byte offsets.** Other coordinates are derived lazily.
9. **New code MUST NOT use ambiguous integer indexing on `text`.** Use bytes, scalar iterators/cursors, grapheme views, or explicit ordinal APIs.
10. **A byte slice MAY become `text` only when both endpoints are proven UTF-8 boundaries.** Otherwise it remains bytes or returns an error.
11. **Sequential iteration MUST be the default Unicode traversal.** Repeated ordinal random access requires an explicit indexed view.
12. **`TextIndex` SHOULD be a valid native byte boundary, not a hidden scalar ordinal.** Next/previous movement must inspect only local UTF-8 bytes.
13. **Sparse indexes SHOULD be lazy and owner-bound.** A process-global manually freed handle map is prohibited for normal text indexing.
14. **A full per-scalar offset table MUST NOT be the default.** It is an explicit workload-specific backend.
15. **Fixed Unicode buffers MUST define capacity in bytes.** `Utf8Buf<N>` maintains a dynamic used length and a valid-UTF-8 invariant.
16. **A fixed “N characters” storage contract MUST NOT assume bounded grapheme size.** Grapheme sequences can expand without a fixed scalar count.
17. **String construction loops MUST use a builder/sink.** Repeated immutable concatenation and repeated placeholder replacement are prohibited in hot paths.
18. **Production transcoding MUST write directly to UTF-8 output.** Intermediate code-point arrays are reference/test tools only.
19. **Streaming decoders MUST preserve state across chunks.** Every short-input partition and output-capacity boundary must be tested.
20. **The scalar implementation MUST remain the semantic oracle.** SIMD/optimized paths must pass differential and fuzz tests.
21. **SIMD completion MUST mean full backend parity and active measured dispatch.** An ASCII-prefix wrapper does not qualify as a complete Unicode kernel.
22. **CPU dispatch MUST be centralized.** Text libraries do not create competing nested dispatch systems.
23. **ASCII fast paths MUST remain explicit and benchmarked.** Adding i18n must not impose locale/Unicode-table cost on ordinary ASCII parsing.
24. **Unicode algorithms MUST use pinned generated data.** Builds expose Unicode and CLDR versions and generator/input hashes.
25. **Automatic normalization of arbitrary `text` is prohibited.** Normalization is explicit; byte equality/hash remains the base contract.
26. **Simple source identifiers MUST use a pinned UAX #31 XID profile and NFC identity.** Original spelling is retained for diagnostics.
27. **Keywords and message keys SHOULD remain ASCII by default.** This minimizes parsing cost and confusable/catalog risk; escaped identifiers remain a controlled option.
28. **String literal content MUST preserve authored scalar sequences except explicit escape decoding.** It is not silently NFC/NFKC normalized.
29. **Grapheme operations MUST follow pinned UAX #29 and live in explicit views/iterators.** They do not redefine compiler or protocol indexing.
30. **Display width MUST require a terminal/layout policy.** It is not a universal property of `text` and must not be used as `len()`.
31. **The current `Name_"..."` i18n syntax SHOULD be preserved.** Localization remains explicit and optional.
32. **The compiler AST extractor MUST be the sole catalog source of truth.** Line/regex scanners may only be audits or delegates.
33. **Persistent message IDs MUST be stable across line movement and unrelated edits.** Scope counters and line numbers are prohibited as IDs.
34. **Message placeholders MUST have a compile-time schema checked across locales.** Missing, extra, or mistyped arguments are build errors.
35. **Plural and select behavior MUST use pinned CLDR rules and a mandatory fallback.** English singular/plural branching is not a general API.
36. **Localized formatting MUST process a compiled message in one pass to a sink.** Runtime repeated string replacement is prohibited.
37. **Core localization APIs MUST accept an explicit locale context.** Thread-local/global locale is a convenience façade only.
38. **User-facing substitutions SHOULD use bidi isolation by policy.** Machine-readable outputs and logs use separate non-display APIs.
39. **An i18n-disabled build MUST have no catalog lookup, registry branch, or locale-data linkage in ordinary string operations.** Optional capability cost stays outside the hot path.
40. **Noalloc profiles MUST declare output capacity and return deterministic capacity errors.** They must never emit malformed partial UTF-8.
41. **The base `text` primitive MUST NOT be duplicated by a second competing `Text` object.** Views, builders, indexes, fixed buffers, and ropes layer on the existing primitive.
42. **SSO and succinct rank/select MUST remain benchmark-gated architecture options.** Neither is assumed beneficial without Simple-specific evidence.
43. **Every text/i18n performance change MUST include before/after evidence.** At minimum report time, throughput, allocations, memory, binary size, corpus, backend, and machine metadata.
44. **Correctness changes and performance changes SHOULD land in separable commits/work packages.** Reviewers must be able to validate semantics before evaluating optimization.
45. **Documentation status MUST be generated or verified against executable tests and dispatch inventory.** A stale “complete” checklist is not release evidence.
46. **Memory performance MUST be gated alongside latency and throughput.** Reviews must report allocation count/bytes, transient workspace, peak and steady RSS, index overhead, and linked Unicode/catalog data for affected profiles.
47. **Optimizations MUST NOT hide memory regressions behind faster wall time.** Any retained, transient, fragmentation, or binary-data increase beyond the calibrated gate requires an explicit tradeoff record.

---

## 21. 2026-08-26 research extension: shaping and Simple 2D/3D rendering

This extension integrates text rendering into the architecture while retaining the repository's existing `shared_multilingual_gpu_fonts` and `simple_2d_vector_fonts` decisions. It does not reopen their canonical renderer/atlas ownership or create a second text object.

### 21.1 Baseline corrections and pinning

- Unicode 17.0.0 is a released baseline, not a draft. The Unicode Consortium released it on 2025-09-09 and published post-release corrections; generation receipts therefore pin input hashes and applied errata in addition to the version label. Sources: <https://www.unicode.org/versions/Unicode17.0.0/>, <https://www.unicode.org/versions/Unicode17.0.0/erratafixed.html>.
- The locale baseline is correctly described as CLDR 48.2.1 data with the LDML 48.2 specification. CLDR 48.2.1 is a data update, not a distinct 48.2.1 LDML specification. Source: <https://cldr.unicode.org/downloads/cldr-48>.
- UAX #29 revision 47 defines the Unicode 17 segmentation baseline and requires a declared default or tailored profile. Official version-pinned conformance files are the acceptance inputs, not hand-selected examples. Sources: <https://www.unicode.org/reports/tr29/tr29-47.html>, <https://www.unicode.org/reports/tr41/>.

### 21.2 Shaping model

HarfBuzz's model confirms that shaping consumes Unicode input plus direction, script, language, features, face, and variation state and produces positioned glyph IDs with clusters. Glyphs are not scalars, and clusters are not interchangeable with grapheme clusters: shaping may map many inputs to one glyph or one input to several glyphs. Source: <https://harfbuzz.github.io/getting-started.html>, <https://harfbuzz.github.io/clusters.html>.

Simple should preserve source UTF-8 byte offsets as logical cluster identities. A shaped run contains glyph IDs, advances, offsets, and logical byte clusters; a separate visual-run order comes from paragraph BiDi resolution. Cursor movement and selection use grapheme boundaries but map through logical clusters. Rendering never reconstructs semantic order from glyph order.

Incremental layout cannot reshape only the edited scalar. Unsafe-to-break and unsafe-to-concat boundaries require expanding an invalidation region to a safe shaping boundary. Shape-plan caches key at least face generation, script, language, direction, features, variation coordinates, and shaper/version. Font fallback decisions additionally key the ordered fallback set and manifest identity. Source: <https://harfbuzz.github.io/shaping-plans-and-caching.html>, <https://harfbuzz.github.io/working-with-harfbuzz-clusters.html>.

### 21.3 Raster and material implications

Shaping and rasterization are separate. The persistent/cacheable shaped run contains no atlas page, UV coordinate, face pointer, GPU handle, or backend resource. Those values are transient `FontRenderer`/`FontRenderBatch` material.

FreeType documents that advance, bitmap bounds, bearings, and glyph bounding boxes are distinct and that hinting can change per-size metrics. Raster cache identity must therefore include face/instance generation, size or projected scale class, variation coordinates, hinting, render mode, transform constraints, and subpixel phase where applicable. Source: <https://freetype.org/freetype2/docs/glyphs/glyphs-3.html>.

Bitmap, vector/path, SDF, MSDF/MTSDF, and color-glyph paint are representation policies, not interchangeable quality levels. SDF/MSDF requires an explicit distance range, scale, edge-coloring/error-correction policy, and overlap handling; it is unsuitable as a universal answer for small hinted UI text or arbitrary color-font paint graphs. Sources: <https://github.com/Chlumsky/msdfgen>, <https://github.com/Chlumsky/msdf-atlas-gen>, <https://harfbuzz.github.io/glyphs-and-rendering.html>.

LCD/subpixel rendering depends on physical pixel order and orientation and is not safe for arbitrary transparency, rotation, perspective, offscreen composition, or 3D surfaces. Those consumers use grayscale/coverage, SDF/MSDF, vector, or color-glyph material under an explicit color-space and blending contract. Source: <https://freetype.org/freetype2/docs/hinting/text-rendering-general.html>.

### 21.4 Canonical 2D flow

The canonical semantic path remains:

```text
Web semantic/layout or GUI widget tree
    -> DrawIrComposition
    -> Engine2D draw_text
    -> text layout/shaping result or handle-free DrawIrGlyphRunPayload
    -> FontRenderer
    -> transient FontRenderBatch and shared atlas
    -> selected CPU/GPU Engine2D backend
```

Unstyled Draw IR remains bitmap-compatible. Producer-resolved shaping is optional but, when present, must round-trip glyph IDs, positions, advances, and logical byte clusters and fail closed if malformed. Draw IR never owns atlas or device material.

### 21.5 Separate Engine3D consumers over shared text material

Engine3D requires several explicit consumer modes:

| Mode | Coordinates and layout | Depth/transform policy | Preferred material |
|---|---|---|---|
| HUD/screen-space | viewport pixels/DPI; 2D line layout | overlay depth policy | bitmap/vector/SDF according to projected size |
| Billboard label | world anchor, screen-facing basis | depth-test/occlusion configurable | SDF/MSDF or vector; grayscale fallback |
| World-plane text | local 2D plane in world transform | full perspective and clipping | SDF/MSDF/vector/color layers |
| Depth-aware annotation | world anchor with leader/layout constraints | visible/occluded/fade policy | same transient material with explicit readback oracle |

These are Engine3D consumers, not alternate GUI/Web/2D routes. They reuse the same segmenter, BiDi/itemization, shaper, fallback resolver, `FontRenderConfig`, glyph identity, `FontRenderer`, atlas owner, and transient batch preparation. A 3D adapter adds model/view/projection, billboard basis, depth policy, projected-size/LOD choice, and 3D instance data. It must not fork shaping, atlas insertion, cache generation, or GPU font programs.

Representation selection for 3D is based on projected pixel size and transform constraints, with hysteresis to avoid LOD thrash. Required tests cover minification, magnification, oblique perspective, near-plane clipping, mirrored/non-uniform transforms, depth rejection, occlusion transitions, device loss, atlas eviction, and stable logical hit/accessibility identity.

### 21.6 BiDi, accessibility, and semantic retention

UAX #9 resolves paragraph direction and visual runs before shaping each direction/script/language run. Logical adjacency, including ZWJ/ZWNJ, remains intact; visual glyph order does not replace logical storage. Localization substitutions prefer isolates. Source: <https://www.unicode.org/reports/tr9/tr9-51.html>.

GPU-rendered text remains semantic text. A rendered surface retains original text or message identity, language, direction, role, logical reading order, selection/caret mapping, and layout bounds for accessibility and test inspection. Atlas pixels alone are never accessibility evidence. Web-facing behavior also covers resize, reflow, and contrast requirements rather than treating a matching bitmap as sufficient. Sources: <https://www.w3.org/TR/wcag/>, <https://www.w3.org/WAI/WCAG22/Understanding/reflow.html>.

### 21.7 Additional performance and coverage findings

Time and memory must be attributed to separate stages: validation/decoding, normalization, segmentation, BiDi, itemization, fallback, shaping, line layout, raster-cache hit/miss, atlas allocation/eviction/upload, batch construction, CPU submission, queue-to-device completion, fence observation, readback, and presentation. Aggregate frame time alone cannot identify regressions.

Rendering evidence records cold and warm p50/p95; input bytes/scalars/graphemes; runs/glyphs; allocations and copied bytes; peak/steady RSS; shaped-run and atlas bytes; eviction/upload bytes; draw calls; CPU/GPU time; projected size; viewport; backend; fallback; checksum/readback; and source/config/manifest identity.

The 100% branch target is structural evidence, not a correctness oracle. It is paired with Unicode conformance files, exhaustive short-input partitions, reference/optimized differential tests, HarfBuzz-compatible glyph/position/cluster witnesses, forced failure/resource-exhaustion cases, and device-origin render parity. Branches proven unreachable by construction require reviewed exclusion evidence; unavailable host/backend rows stay blocked and are never reclassified as covered.

### 21.8 Current rendering and evidence audit

The current repository already has the intended high-level ownership but not the complete behavior:

- `src/lib/common/ui/draw_ir.spl` defines handle-free `DrawIrGlyphRunPayload`, while widget, WM, and Web producers emit `DrawIrComposition`; `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` selects shaped/resolved/plain lowering into the canonical Engine2D font path.
- Web RTL paint currently reverses text rather than implementing full UAX #9 itemization/shaping, and wrapped vector/shaped metrics are disabled in a key path. GUI fallback may synthesize 5x7 glyph IDs with ordinal clusters rather than source UTF-8 byte clusters.
- `FontRenderer` owns the persistent atlas and staged transient material, but `FontRenderBatch` carries full atlas pixels. Copy/borrowing semantics, dirty rectangles, maximum transfer size, generation lifetime, and noalloc behavior require measurement and a stricter contract.
- Engine3D has shared `FontRenderer`/`FontRenderBatch` HUD and projected-world entrypoints, but current world text projects one anchor and emits screen-space quads at constant depth. CPU fallback draws it as HUD. There is no complete billboard/world-plane transform, projected-size LOD, multiline world bounds, or CPU depth/occlusion parity.
- The Vulkan Engine3D font adapter owns sibling-private pipelines and resources correctly, but uses a separate font-only target, uploads the full atlas after changes, and allocates a native vertex buffer per draw. A readback therefore does not yet prove scene-plus-text composition.
- Legacy `nogc_sync_mut/engine/render/text.spl` and its ASCII atlas remain separate compatibility paths and must converge on or delegate to the canonical font owner rather than receive new international-text behavior independently.
- Existing shared-font specs contain the five primary phrases, but the “2D and 3D” step presently compares Engine2D CPU/SIMD rather than proving one immutable batch consumed by Engine2D and Engine3D.
- The compiler now has a canonical flat-AST zero-count inventory and the test runner pre-registers it before merging runtime outcomes, so wholly unvisited Simple decisions can remain in the denominator. Focused inventory and aggregation tests passed on 2026-08-26. Retained production-owner results now include `src/lib/common/string_core.spl` at 280/280 examples and 100% branch coverage (52/52), with line coverage separately at 98% (158/160); `src/lib/common/encoding/utf16.spl` at 40/40 examples, 100% line coverage (85/85), and 100% branch coverage (23/23); and `src/lib/common/encoding/utf32.spl` at 27/27 examples, 100% line coverage (60/60), and 100% branch coverage (16/16). The UTF-8 reference owner is separately retained at 97% branch coverage (41/42); its final guard is unreachable through valid `text` but remains necessary while unchecked byte-to-text construction exists. No retained aggregate yet scopes every text/i18n/rendering owner or merges Rust/C/SIMD/GPU branch evidence, so these owner results do not prove the requested all-owner 100% coverage. The UTF-32 memory lane now emits endian-roundtrip and UTF-8 conversion receipts over 8,190 multilingual scalars, but the interpreter exposes neither allocation counters nor process HWM; zero-valued internal counters are classified as unavailable. Shared-font performance was aborted because unrelated host work consumed about 18 GiB RSS at full CPU, and a later UTF-16 measurement was withheld at host load averages 27.45/35.05/26.88; latency and RSS comparisons are inadmissible under either condition. Engine3D still lacks retained HUD/world latency, throughput, allocation, RSS, and device-memory rows on a controlled host.

- The generic codec’s bytewise reconstruction defect is now fixed in the working tree: decoded scalar values are handed to validated UTF-8 reconstruction, and ASCII replacement occurs once per unsupported scalar. The focused suite passes 30/30 multilingual, malformed, endian, alias, and helper-policy examples. Its third/final owner result is 94% line coverage (93/98) and 45% branch coverage (29/64), not 100%; short-circuit alias combinations account for many unclosed paths. The architecture findings still hold: unknown labels retain the legacy UTF-8 fallback, and UTF-16/32 conversion retains O(scalar-count) intermediate arrays until the direct streaming `TextSink` implementation lands.

- The retained resource-bundle tests previously did not test the resource bundle: 33 examples asserted locally assigned constants while claiming 80% coverage for two production owners. A new direct production suite passes 13/13 and measures the real `src/lib/nogc_sync_mut/i18n/bundle.spl` at 52% lines (50/95) and 92% branches (13/14). The byte-identical `src/std/nogc_sync_mut/i18n/bundle.spl` shadow receives no hits even when explicitly instrumented, exposing a module-identity and duplicate-owner defect that must be resolved before aggregate coverage. A new memory lane records 4,096 real lookups and 512 Arabic two-argument formatting calls, but runtime allocation and HWM counters remain unavailable; the current repeated-`replace` formatter is therefore neither allocation- nor RSS-qualified.

- The shared font-atlas composite owner now has a bounded 7/7 suite covering cache identity, invalid geometry, overflow, source storage, alpha tinting, destination bounds, versioning, and all generated backend sources. Its Simple decision coverage is 100% (10/10), with line coverage 32% (35/107). This does not cover branches embedded inside the generated OpenCL/HIP/CUDA/Metal/GLSL source strings. A CPU memory lane processes 1,048,576 extracted output bytes and preserves separate Engine2D/Engine3D cache identities, but allocation/RSS and device memory/upload/queue/readback remain unavailable and must not be inferred from CPU reference pixels.

These are implementation blockers, not reasons to fork the architecture. The new plans reuse the existing static Simple branch inventory and add all-owner/native-backend closure, fault injection, shared batch identity, real scene depth composition, dirty atlas transfer, frame arenas/ring buffers, and separate native device receipts.
