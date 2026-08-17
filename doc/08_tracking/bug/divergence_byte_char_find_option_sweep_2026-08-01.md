# Divergence sweep: byte-vs-char + find/rfind-as-Option — IN PROGRESS

- **Id:** divergence_byte_char_find_option_sweep_2026-08-01
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** P2 — silent product-correctness divergences across `src/**`
- **Component:** cross-cutting (`src/compiler`, `src/lib`, `src/app`)

## Scope

Cheap read-only parallel scans (small models) over the owned tree, oracle-verified
per finding against the Rust seed, fixing silent divergence-family bugs:
- **byte-vs-char** — `text.len()` (bytes) mixed with char-indexed `[i]`/`char_at`/
  `char_code_at`; fix = `.chars()` (char-array) or `slice(i,i+1)` (byte-consistency).
- **find/rfind/index_of as Option** — they return a raw i64 (-1 = miss), NOT an
  Option; `if val`/`.?`/`match Some/nil`/`?? default` all misbehave. Additionally
  the tag-boxed result slices wrong as a `text[:idx]` bound — use `.substring()`.

## Landed so far (2026-08-01)

- `4beaa207810` — JS delimiter gate + SQL LIKE prefix/matcher (3 fixes)
- `29687ff0d530` — treesitter heuristic + macro_registry expand (2 fixes)
- `30fbcdc0f00` — find→bracket-slice family enumerated (5 more sites: KMS SigV4,
  formatter, doc_gen, infra, deployment automation)
- (earlier waves this session: `95bab2150be`, `4149aa7d01b`, `62dc9efd4ad`)

## Not yet done

- Scan coverage is not exhaustive: several `src/lib` / `src/compiler` subtrees
  remain unscanned; yield is decreasing (Wave 11 = 2 fixes / 5 lanes, 3 clean)
  but not zero. Continue in waves until a full pass returns clean.
- Deferred site: `module_lowering.spl:176` (native-codegen-sensitive) — see
  `doc/08_tracking/bug/module_lowering_byte_vs_char_sanitizer_2026-08-01.md`.
- Byte-semantic rewrites (to_bytes/base64/checksum/crypto signing) still need a
  real UTF-8 byte accessor; the char-array fix yields codepoints, not bytes.

This sweep is product-correctness only; it does **not** unblock pure-Simple
self-host (that umbrella blocker is
`doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`).

## Wave 2026-08-02 — re-derived census, markdown scanner fix, two refuted claims

### Landed

- `7a6e4b5756d` — `markdown_inline_text` / `markdown_plain_inline`
  (`src/lib/common/markdown/inline.spl`) made BYTE-indexed end to end, plus 17
  regression examples in `test/01_unit/lib/common/markdown/markdown_spec.spl`.

  Hand-computed exemplar, input `"\u{e9}*x*"` = 5 BYTES (`C3 A9 2A 78 2A`) but
  4 CHARACTERS: the loop bound `n = value.len()` counted bytes, the marker scan
  used `char_at` (characters), so the italic interior came out as
  `value.slice(2, 3)` = `"*"` instead of `"x"`, and the byte-bounded loop then
  ran one index past the last character where `char_at` returns nil.
  Fix: index bytes throughout. Every inline marker is ASCII (< 0x80) and UTF-8
  is self-synchronizing (continuation bytes are always >= 0x80), so a byte scan
  can never mistake part of a multi-byte character for a marker; literal text
  advances by the whole `utf8_seq_len` sequence.

  Non-vacuity PROVED by sabotage: with the previous implementation restored,
  9 of the 17 new examples fail and both ASCII controls stay green — the tests
  discriminate on the non-ASCII axis, not on the code merely running. The other
  8 examples pass either way and are documentation, not detectors.

- `c37b573141` — `strip_html_tags` made BYTE-indexed in all three layer clones
  (`gc_async_mut` / `nogc_async_mut` / `nogc_sync_mut` `security/sanitize.spl`),
  plus a new fast unit spec `test/01_unit/lib/security_sanitize_utf8_spec.spl`.

  This one is a sanitizer correctness failure, not just mojibake. The loop
  pushed `input.slice(i, i + 1)` -- a SINGLE BYTE -- at a character index, so
  (a) every multi-byte character left as an isolated lead byte (invalid UTF-8)
  and (b) the byte-bounded loop desynced the `in_tag` state machine and TAG
  FRAGMENTS LEAKED THROUGH. Observed on the shipped function:
  `strip_html_tags("<p>\u{e9}</p>")` returned a broken byte followed by a
  literal `>`, and `"<b>caf\u{e9}</b> <i>\u{4e2d}</i>"` returned
  `caf?>>/i>` -- three leaked tag fragments.

  Non-vacuity proved by sabotage through the spec harness: with the previous
  implementation restored, 7 of the 8 examples fail (including the explicit
  "no `>` leaks" assertion) and the ASCII control stays green.

### Census re-derivation (PROVED, reproducible)

Earlier waves carried an inferred figure of ~891 remaining sites. Re-derived
from scratch with stated predicates over owned `.spl` source (vendor excluded),
that figure does not reproduce. Two distinct forms, counted separately:

- **FORM A** — a bound derived from `RECV.len()` (BYTES) driving
  `RECV.char_at(i)` / `RECV.char_code_at(i)` (CHARACTERS), same receiver token,
  same function body: **371 sites / 303 functions / 161 files**.
- **FORM B** — a shared index atom flowing into BOTH a character accessor and a
  byte accessor (`slice` / `substring` / `byte_at`) on the same receiver inside
  one function: **80 pairs / 49 functions / 36 files**.

Predicate sensitivity, so the number is not a lucky threshold:

| tightening level | count |
|---|---|
| files containing both index spaces | 281 |
| functions containing both | 193 |
| + same receiver token | 158 |
| + shared index atom (FORM B census) | 61 unique tuples / 80 pairs |

Raw accessor calls for scale: 1,278 character-space, 7,769 byte-space (the
byte-space figure includes ARRAY `slice`, which is element-indexed and NOT part
of this family — a large share of any raw `slice` count is not a defect).
Pair counts also over-report: the 18 FORM B pairs in `markdown/inline.spl` are
2 functions. **Functions, not pairs, is the honest unit.**

Scripts: the census is a pure static scan; the predicate is stated above and was
run against `7a9b60a859e` in an isolated checkout.

### Refuted claims (negative results)

- **"Byte-semantic rewrites still need a real UTF-8 byte accessor"** (§ Not yet
  done, above) — REFUTED. `byte_at` already exists in every runtime layer:
  `src/runtime/runtime_native.c:2372` (C), `src/runtime/simple_core/core_string.spl:351`
  (pure-Simple), `src/compiler_rust/runtime/src/value/collections.rs:3048` (Rust),
  and as an `extern` in the interpreter. The markdown fix above is built on it.
  No new accessor is needed for byte-semantic rewrites.

- **`SIMPLE_UTF8_SLICE_AUDIT` is INERT in the deployed binary** — the audit
  module (`src/compiler_rust/runtime/src/text_slice_audit.rs`) exists in source,
  but the string `SIMPLE_UTF8_SLICE_AUDIT` does not appear anywhere in
  `bin/release/x86_64-unknown-linux-gnu/simple` (0 occurrences, binary dated
  2026-08-02). Setting the env var is a no-op there, and the module's own
  liveness self-test — which is designed to emit one synthetic violation per
  enabled process precisely so a vacuous zero is detectable — does not fire.
  **Any "zero violations" measured through the deployed binary is vacuous.**
  The instrument must be rebuilt into the shipped tool before its counts mean
  anything.

### Index-space contract (confirmed empirically, hand-computed expectations)

Probed on `"h\u{e9}llo"` = 6 BYTES / 5 CHARACTERS; every value below was
predicted from the UTF-8 encoding before running anything, and matched:

| expression | value | space |
|---|---|---|
| `.len()` | 6 | BYTES |
| `.char_code_at(1)` | 233 (`é`) | CHARACTERS |
| `.byte_at(1)` | 195 (`0xC3` lead) | BYTES |
| `.byte_at(2)` | 169 (`0xA9` cont.) | BYTES |
| `.char_code_at(4)` | 111 (`o`) | CHARACTERS |
| `.char_code_at(5)` | 0 (no 6th char) | — overrun of a `len()`-bounded loop |
| `.slice(0, 2)` | 2 bytes `68 C3` | BYTES — invalid UTF-8 |

So a `len()`-bounded loop over-iterates by exactly (bytes - characters), and the
tail iterations read past the last character. This is the FORM A mechanism.

### Triage — three buckets, counted

Buckets: **(1) genuinely wrong** on non-ASCII input; **(2) correct-by-accident**
(mix is real but the receiver is ASCII-only in practice, so it cannot misbehave
today); **(3) false positive** of the scan itself.

**FORM B — all 49 functions inspected individually:**

| bucket | count |
|---|---|
| 1 genuinely wrong | 30 |
| 2 correct-by-accident | 16 |
| 3 false positive | 1 |
| already fixed this wave | 2 |

The single bucket-3 is `llm_caret/.../termio/parser.spl:findSequenceEnd`, where
the character and byte calls sit in mutually exclusive branches and never share
a live index (a separate FORM A defect does remain in that function).

**FORM A — random sample of 40 of the 371 sites** (indices recorded in the wave
notes; sampled rather than exhaustive because 371 is not hand-verifiable in one
pass):

| bucket | count | rate |
|---|---|---|
| 1 genuinely wrong | 17 | 42.5% |
| 2 correct-by-accident | 23 | 57.5% |
| 3 false positive | 0 | 0% |

Extrapolated ≈ **158 of 371** FORM A sites genuinely wrong (rough 95% interval
110-210). This is an EXTRAPOLATION from a 40-site sample, not a verified count.

Bucket 2 is dominated by one honest pattern: digit / hex / ASCII-token scanners
(`_parse_i64`, `_parse_hex_int`, `parse_cell_ref`, IPv4 and `max-age`
validators) where a non-ASCII byte is rejected or ignored identically in either
index space. Converting those is churn, not a fix.

**Scan-quality findings (reported, not hidden):** pair counts over-report badly
(18 FORM B pairs in `markdown/inline.spl` are 2 functions); the FORM A scan
double-counts two lines of one function as two sites, mislabels the enclosing
`fn` on at least two sites, and one FORM A site duplicates a FORM B site.
Function count, not site or pair count, is the trustworthy unit.

**Undecided, filed rather than guessed:**

- `src/os/crypto/pem.spl:167,227-237` (`pem_decode`, `pem_decode_all`). RFC 7468
  preamble text between blocks is commonly non-ASCII (openssl subject lines), so
  `char_at(body_start)` can read right of the intended byte, into the wrapped
  base64 body. Usually harmless (the redundant newline skip simply does not
  fire, and `line_unwrap`/`_trim_text` clean up), but base64 carries a `\n` every
  ~65 characters, so there is a roughly 1-in-65 chance the probe hits `"\n"`,
  drops the first base64 character and silently corrupts the decoded DER.
  Classified bucket 2 on practice; NOT provably safe. Needs a decision from
  someone who owns the PEM contract.
- `.../model_loader/manifest.spl:122,203` — safetensors headers are ASCII in
  every observed sample, but `__metadata__` is a free-form JSON string map; a
  model shipping a UTF-8 description desyncs `_array_body` / `_shape_field`.
  Classified 2 on practice, not on proof.

### Remaining genuinely-wrong sites, ranked (NOT yet fixed)

1. `src/lib/editor/services/lsp_transport.spl:358` `_lsp_transport_escape` —
   `char_at` past the character count returns NIL and `nil + text` collapses the
   whole accumulator, so an LSP payload containing any non-ASCII character is
   lost entirely. Input `"\u{e9}"` = 2 BYTES / 1 CHARACTER.
2. `src/compiler_rust/lib/std/src/mcp/simple_lang/dependencies.spl:448-458`
   `contains_symbol` — byte match offset used for a character-space word-boundary
   test, so a present symbol is reported absent.
3. `src/lib/common/js/engine/lexer.spl:204` `_unescape_string` — `\uXXXX` read
   with a byte slice at a character index; the hardcoded `é`/`世`/`界` cases at
   :207-212 are an existing band-aid over exactly this.
4. `src/lib/common/archive/zip.spl:53` `_ascii_to_bytes` — used for entry names
   AND `ZipFile.data`, so archived UTF-8 content is written as codepoint-mod-256
   plus overrun garbage.
5. `src/lib/editor/services/command_palette.spl:40` `fuzzy_match` — compares a
   character counter to a byte length, so any non-ASCII query can never match.
6. `.../browser_engine/script/js_transpiler.spl:236` `_safe_replace` and
   `:210-220` `_convert_line_comment` — a JS line containing non-ASCII returns
   nil, silently deleting the line from transpiled output.
7. `src/lib/common/markdown/adapter.spl:182,186` `_adapt_trim`.
8. `src/lib/gc_async_mut/http_client/types.spl:67` `url_decode` (two lanes).

The nil-collapse mechanism behind 1, 4 and 6 is worth stating once: `char_at`
returns NIL past the character count and string concatenation with nil yields
nil, so a byte-bounded loop that CONCATENATES `char_at(i)` does not merely
mis-slice — it destroys the entire accumulated result. Loops that only COMPARE
`char_at(i)` degrade harmlessly, which is why bucket 2 is as large as it is.

## Wave 2026-08-02b — ranked remainder, the blind spec tier, the inert instrument

### The measurement finding that reframes this whole sweep

**sspec `describe` blocks CANNOT observe the nil-collapse form of this defect.**
Proved by discriminating probes against the shipped binary, not inferred:

| expression | `simple run` | inside sspec TEST |
|---|---|---|
| byte-bounded `char_at` concat of `"\u{e9}"`, `.len()` | **-1** (nil sentinel) | **2** |
| `expect(false).to_equal(true)` | — | correctly FAILS |

So `accumulator + nil` is a no-op on the sspec tier and nil-collapsing on the
run tier. The DSL is sound — the sanity controls fail correctly — the *tier* is
different. `SIMPLE_EXECUTION_MODE` does not move it: set to `jit`, `native` and
`llvm` in turn, an example asserting the -1 sentinel failed and one asserting 2
passed in **all three** runs.

**Consequence: this lane's first sabotage run came back GREEN against the
known-broken `_lsp_transport_escape`.** A spec-based regression for sites 1, 4
and 6 of the ranked list is structurally vacuous. Regression cover for the
nil-collapse family therefore lives in
`test/01_unit/bugs/utf8_index_space_jit_probe.spl`, a runnable program in the
convention of `text_ordering_jit_probe.spl`, not in a `describe`. **There is no
CI hook that runs `*_jit_probe.spl` files** — neither the pre-existing probe nor
this one — which is an open gap, recorded here rather than papered over.

Second trap, same class: **a driver `.spl` placed OUTSIDE the repo tree resolves
`std.*` against a different source root.** Running one from the scratch
directory silently measured an unedited copy of the library and made a correct
fix look like it had failed. Run probes from the repository root.

### Landed this wave

- `1ba2e7af34a` — `_lsp_transport_escape` (ranked #1). PROVED on the shipped
  module: every non-ASCII input returned the -1 nil-length sentinel — the whole
  LSP payload destroyed, not one character mangled — while the ASCII control
  returned a correct 4. All four public builders (didOpen, didChange,
  workspace/symbol, rename) shown dropping their content. Sabotage: 13 checks
  flip red under `SIMPLE_EXECUTION_MODE=jit`, ASCII controls stay green.
- `e16517c5454` — `fuzzy_match` + `fuzzy_score` (ranked #5, **partly refuted**,
  see below).
- `c4a748ab774` — safetensors `_array_body` and the shape-field scanner
  (previously undecided, now **decided as genuinely wrong**).
- `dc002baecf9` — `pem.spl` (previously undecided, now **proved safe**, and
  `_trim_text` in the same file fixed as a genuine defect).
- `scripts/check/check-utf8-slice-audit-live.shs` — makes the inert audit loud.

### Refuted this wave

- **Ranked #5 `fuzzy_match` "any non-ASCII query can never match" — REFUTED.**
  It matched. Past the character count BOTH `char_at` calls return nil and
  `nil == nil` is TRUE, so each surplus query byte is consumed by a free
  nil-match; a candidate containing the query always carries at least as much
  byte surplus as the query, so the accident holds and the boolean answer was
  already correct. Correct-by-accident, not correct-by-design.
  What IS genuinely wrong is the **score**, because each free nil-match also
  paid `10 + streak`. Measured for query `é`, before → after:
  `"café"` 20→8, `"éa"` 21→11, `"中é"` 22→10, `"xxé"` 21→9. Before the fix
  `"中é"` (match at position 1) **outranked** `"éa"` (match at position 0)
  purely because the candidate held a 3-byte character. The palette ordered
  results by character WIDTH. ASCII scores are unchanged by the fix.
- **`pem.spl` "roughly 1-in-65 chance of dropping a base64 character" —
  REFUTED for RFC 7468 conformant input.** For the skewed newline probe to drop
  base64 it must skip when `body_start` already points at base64. It cannot:
  RFC 7468 requires an EOL immediately after the BEGIN marker, so that byte is
  always CR or LF, and with 64-character wrapping the skewed read lands on a
  base64 character, matching neither. The misread makes the code skip LESS,
  never more, and a retained leading newline is removed by `line_unwrap` /
  `_trim_text`. Fixed anyway, as hardening, to remove the accident.
  The genuine defect in that file is `_trim_text`: on `"  \u{e9}"` (4 BYTES /
  3 CHARACTERS) it returned only the LEAD BYTE of the `é` — invalid UTF-8 fed
  to a base64 decoder.

### `SIMPLE_UTF8_SLICE_AUDIT` — the mechanism, and the exact fix

Not compiled out, and not unwired. `runtime/src/lib.rs` declares
`pub mod text_slice_audit;` **unconditionally, with no `cfg` gate**, and three
call sites reference it unconditionally (`interpreter/expr/collections.rs:934`,
`interpreter_method/string.rs:331`, `runtime/src/value/collections.rs:3989`).
The module landed in `2ca6b4da3a9` on 2026-08-01 and `git cat-file -t` confirms
it is an ancestor of `main`.

It was **LOST IN DEPLOYMENT**: `bin/release/x86_64-unknown-linux-gnu/simple` was
never rebuilt from a tree containing it. Two independent measurements:

- static — `SIMPLE_UTF8_SLICE_AUDIT`, `interp_bracket`, `interp_method`,
  `rt_slice_rust` and `self_test` all occur **0** times in the binary, while the
  control string `SIMPLE_EXECUTION_MODE` occurs **3** times, so the absence is
  real and not an artifact of the search;
- dynamic — with `SIMPLE_UTF8_SLICE_AUDIT=1` and `=2` the binary emitted **0**
  audit lines, so the module's own once-per-process `site=self_test` liveness
  violation — built precisely to distinguish a real zero from an inert one —
  never fired.

**Exact fix: rebuild the Rust runtime and redeploy the seed binary.** That is
another lane's; it was NOT run here. Until it happens,
`scripts/check/check-utf8-slice-audit-live.shs` fails loudly (exit 1) on both
the static and the dynamic check, so the instrument can no longer report a
vacuous clean. It also fails closed when no binary is found, and aborts when its
own control string is missing.

### Remaining genuinely-wrong sites, ranked (still NOT fixed)

Numbering follows the previous wave. #1 and #5 landed; #5 with the refutation
above. The rest are untouched and carry their mechanisms:

2. `src/compiler_rust/lib/std/src/mcp/simple_lang/dependencies.spl:448-458`
   `contains_symbol` — `text.substring(i, i + symbol.len())` matches at a BYTE
   offset `i`, then `text.char_at(i - 1)` / `char_at(i + symbol.len())` use that
   same `i` as a CHARACTER offset for the word-boundary test. With any non-ASCII
   earlier in the haystack the boundary probe reads the wrong character, so a
   present symbol is reported absent (or an embedded one reported present).
3. `src/lib/common/js/engine/lexer.spl:204` `_unescape_string` — `\uXXXX` is
   read with `raw.slice(i + 1, i + 5)`, a BYTE slice, at a CHARACTER index `i`.
   The hardcoded `é` / `世` / `界` special cases at :207-212 are an existing
   band-aid over exactly this and should be deleted by the fix, not kept.
4. `src/lib/common/archive/zip.spl:53` `_ascii_to_bytes` — byte-bounded loop
   over `char_at`, then `char_code_at(0).to_u8()`, i.e. codepoint-mod-256 plus
   overrun garbage. Used for entry names AND `ZipFile.data` (:297), so archived
   UTF-8 CONTENT is corrupted, not just filenames. Needs a real UTF-8 encoder,
   not an index-space swap — the widest of the remaining items.
6. `.../browser_engine/script/js_transpiler.spl:236` `_safe_replace` and
   `:210-220` `_convert_line_comment` — nil-collapse family: a JS line
   containing non-ASCII returns nil, silently DELETING the line from transpiled
   output. Verify with the runnable probe, never a `describe`.
7. `src/lib/common/markdown/adapter.spl:182,186` `_adapt_trim` — same shape as
   the `pem.spl` `_trim_text` fixed this wave (BYTE `start`/`end` bounds read
   with `char_at`, result taken with `slice`), so the fix there is the template.
8. `src/lib/gc_async_mut/http_client/types.spl:67` `url_decode` — `len` is
   `text.length()` (BYTES) while `text.char_at(i)` is CHARACTERS, and the `%XX`
   branch takes `substring(i + 1, i + 3)` in byte space off the same `i`.

Sites 2, 3, 6, 7 and 8 are index-space swaps of the kind already landed five
times; site 4 needs an encoder and should be scoped separately.
