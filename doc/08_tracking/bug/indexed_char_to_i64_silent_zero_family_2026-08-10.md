# `s[i].to_i64()` on a string-indexed char silently returns 0 — family census

## Policy re-check 2026-11-02 (lane a6dffc9c/p12-6)

**Checked against current policy/design: re-scoped to: indexed characters from `text[i]` are ambiguous (`'7'.to_i64()` = 7, not 55; JIT 0 vs interpreter code point for non-digits) because there is no distinct `char` type**

Policy: nil only inside `unsafe`, `Option`/`None` elsewhere; no `Any` outside `unsafe`; erased generics (no monomorphization); TDD.

Measured at 2345aff3ff5: `val c = "A"[0]; c.to_i64()` was `65` on the interpreter
(commit `8d100a8aa81`) but `0` on the JIT (`rt_string_to_int` returned 0 for any
non-numeric text) - a silent cross-engine wrong answer.

- **Not changed (review decision, PR #5924):** an attempt to make the shared
  `rt_string_to_int` return a code point for a single non-numeric character was
  reverted. That function backs ALL text-to-int conversion, so
  `"x".to_i64()` on single-character user input would silently become 120, a new
  silent-wrong-value class, and the Rust runtime would diverge from the C twin
  (`src/runtime/runtime_native.c:7539`). The JIT therefore still returns 0 for
  `"A"[0].to_i64()` while the interpreter returns 65 (`8d100a8aa81`).
- **Scope now:** indexing a `text` still yields `text`, so any indexed character
  is ambiguous (non-digit: 0 on the JIT / code point on the interpreter; digit: `"7"[0].to_i64()` is `7`, not the code point `55`);
  `char_code_at` is the unambiguous API, guarded by
  `scripts/check/check-string-index-char-to-i64.shs`). The fix belongs at the type level: a distinct
  `char` type from `text[i]` in HIR (the cited `hir/lower/expr/index.rs` site),
  or making callers use `char_code_at` - a language/type-system decision; a
  difficulty-3 row records it.
- Policy interaction: none of nil/Any/erasure is involved; this is not obsoleted
  by the Option policy. Severity stays P1 (the seed JIT/interpreter divergence is unfixed).

Evidence (this lane): debug Rust seed built from `2345aff3ff5`
(`cargo build -p simple-driver`, `CARGO_TARGET_DIR=C:/dev/wt/p12-6/target-p12`), JIT
= `simple run`, interpreter = `SIMPLE_EXECUTION_MODE=interpret simple run`.
(No test for this bug: no runtime change was made.)

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

**Filed:** 2026-08-10
**Parent:** `blink_selector_engine_totally_red_and_dom_node_builder_missing_2026-08-10.md` (Defect 2)
Status: OPEN (P1) — RE-SCOPED 2026-11-02 (type-level: no char type from text[i]; no runtime change made)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Defect

On the interpreter lane, indexing a **String** and calling `.to_i64()` returns
**0 for every character**, with no diagnostic:

```
val s = "div"
print(s[0].to_i64())       # 0     <-- WRONG
print(s.char_code_at(0))   # 100   <-- correct
```

Any char-classification code using this pattern treats every byte as NUL and
produces garbage silently. `char_code_at(i)` is the correct call.

## Family size (raw census, 2026-08-10)

Pattern `\[[A-Za-z_0-9 +\-]+\]\.to_i64\(\)` over `src/lib` (via `/usr/bin/grep`,
vendor excluded):

- **454 sites in 119 files.**

**CAUTION — the raw count overcounts.** Many hits index a `[u8]`/`[i64]` list
(e.g. compress/, crypto/, hpack/), where `.to_i64()` on the element is a
widening no-op and NOT affected. The dangerous subset is only where the indexed
receiver is a **String/text**. Grep cannot separate the two; triage needs type
information (LSP `lsp_type_at` or a compiler-assisted sweep). Heavy suspects
(string-parsing modules): `common/sdn/parser.spl`, `common/encoding/base58.spl`,
`common/web/browser_renderer_protocol.spl` (36 hits),
`gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer*.spl`,
`nogc_*/net/telnet.spl`, `nogc_sync_mut/mcp_sdk/core/json.spl`.

## Type-aware triage (2026-08-10)

**Corrected semantics:** `s[i].to_i64()` is parse-as-integer on the 1-char
string: digit chars return their numeric value (`"7"` → 7), non-digits → 0.
`[u8]`/`[i64]` element `.to_i64()` widens correctly. So the dangerous subset is
string-indexed sites that expect a **char code**.

**Method:** declaration-resolving classifier (scratchpad script): for each
`recv[idx].to_i64()` site, resolve `recv`'s type from in-file declarations /
params / producer calls (`: text|String`, `= "..."`, `.split(` → `[text]`,
`: [u8]`, `.to_bytes()`/`rt_string_bytes`/etc. → bytes). Calibrated: the 8
known-dangerous pre-fix `selector.spl` sites classify STRING (7) / UNKNOWN (1,
aliasing); known `[u8]` sites (`compress/snappy.spl`) classify BYTES.

**Census (src/lib, live tree):** 548 raw sites, 123 files →
- BYTES (benign widening): 379
- LIST_TEXT (split-parts whole-string parse — benign, correct usage): 74
- UNKNOWN: 89 — all manually resolved to byte-producing receivers (gzip
  `data`, `rt_string_bytes`, `text_to_bytes`, sha/aes/lzma/x25519 buffers,
  arena reads, int-count lists) or split-field parses; none dangerous.
- **STRING-dangerous: 6 sites in 5 files** (all fixed, below).

Named suspects cleared: `sdn/parser` (byte lists), `base58` (sha256 checksum
bytes), `browser_renderer_protocol` (36 hits = split-field parses with
`str(count) != field` guards — correct), `telnet` (bytes), `mcp_sdk/core/json`
(`rt_string_bytes` output).

## Fixed 2026-08-10 (this triage)

- `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/io/string_helpers.spl`
  `char_code()` — returned 0 for `"A"` (doc promises 65). → `char_code_at(0)`.
  New sabotage-sensitive spec: `test/01_unit/lib/io/string_helpers_char_code_spec.spl`.
- `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl`
  (2 sites) — digit-validation loops `c < 48 or c > 57` rejected EVERY digit
  (parse gives 7, not 55), so `_json_i64` returned 0 for all numeric tokens.
  Spec `chrome_webgpu_draw_evidence_spec.spl` is sabotage-sensitive (9→8).
- `src/lib/nogc_sync_mut/http_server/h2_server.spl` `_text_to_u8` — emitted
  0/digit-value bytes instead of char codes. Existing h2 specs do NOT cover it
  (sabotage stays green); new spec `test/unit/lib/http/h2/h2_server_text_to_u8_spec.spl`.

No compensating-zero sites found: none of the 6 depended on the wrong value.

## Fixed so far

- `src/lib/blink/css_parser/selector.spl` — all 8 string-index sites converted
  to `char_code_at`; sabotage-verified (reverting one site flips the two
  combinator examples in `css_selector_spec.spl` RED).

## Gap analysis + guard (2026-08-10)

Nothing caught the family because (a) the failure is silent — parse-as-integer
returns a plausible 0/digit instead of erroring; (b) most consumers had no
spec at all (`char_code` had a spec that never called it on a non-digit;
`_text_to_u8` had zero coverage); (c) no scanner existed.

Guard added: `scripts/check/check-string-index-char-to-i64.shs` — same
declaration-resolving classifier in awk. Fail-closed: verdict line states the
scanned site count; a planted control fixture (a `s: text` indexed
`.to_i64()` site) must be detected or the run is ERROR exit 2; scans ALL of
`src/lib` with no directory exclusions. Verified: PASS — 541 sites scanned on
the fixed tree; re-sabotaging one live site flips it to FAIL with the exact
file:line.

## Language-level fix (the real one)

`.to_i64()` on an indexed char should either return the code point or be a
compile/runtime error. Silently returning 0 is the worst option. Until then,
consider a lint/fence for `<string-typed>[i].to_i64()` once type-aware scanning
is available.

## Design check 2026-11-03: BLOCKED-ON-DESIGN

No decided `text[i]` result type exists in doc/04_architecture, doc/05_design or doc/07_guide/language.
`doc/05_design/compiler/char_utf8_storage_compatibility_20261019.md` plans physical Char storage but is
NOT IMPLEMENTED, and says nothing on what `text[i]` yields. No parity fix landed (would need a type decision).
Options for the owner:
1. `text[i]` yields `char` (HIR type in `hir/lower/expr/index.rs`, plus runtime ABI); `char.to_i64()` = code point on both engines. Needs the Char UTF8 plan above first.
2. Keep `text[i]` as `text`; make `.to_i64()` on text parse-only (JIT and interpreter both 0/None for non-numeric) and require `char_code_at` for code points. Interpreter change only; guard `check-string-index-char-to-i64.shs`.
3. Lint/diagnose `text[i].to_i64()` at compile time (steer to `char_code_at`), no semantic change.
Recommendation: option 3 now, option 1 after the Char plan lands.
