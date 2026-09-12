# `s[i].to_i64()` on a string-indexed char silently returns 0 — family census

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

**Filed:** 2026-08-10
**Parent:** `blink_selector_engine_totally_red_and_dom_node_builder_missing_2026-08-10.md` (Defect 2)
Status: OPEN (P1)
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

## Triage 2026-09-12 — still OPEN, and the characterization above is now WRONG

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).
Identical results on `SIMPLE_EXECUTION_MODE=jit` and `=interpreter`.

Repro (one file):

```simple
fn probe() -> str:
    val a: text = "A"
    val d: text = "7"
    val s = "A7"
    return "textA=" + str(a.to_i64()) + " text7=" + str(d.to_i64())
         + " idxA=" + str(s[0].to_i64()) + " idx7=" + str(s[1].to_i64())
         + " charatA=" + str(s.char_at(0).to_i64()) + " charat7=" + str(s.char_at(1).to_i64())
         + " multi=" + str("12".to_i64())
print probe()
```

```
textA=65 text7=7 idxA=65 idx7=7 charatA=nil charat7=7 multi=12
```

**"Returns 0 for every character" no longer holds.** The title and the Defect
section are stale. What the deployed seed actually does is worse to reason
about, because one expression shape now has **three** different answers:

| expression | `"A"` (non-numeric) | `"7"` (numeric) |
|---|---|---|
| `(x: text).to_i64()` | **65** — the code point | 7 — parsed |
| `s[i].to_i64()` | **65** — the code point | 7 — parsed |
| `s.char_at(i).to_i64()` | **nil** | 7 — parsed |

So: indexing agrees with a plain `text` receiver, `char_at` does not, and the
*same receiver* silently switches between "parse me as a number" and "give me
my code point" based on the character's own content. The digit case is the
dangerous one and is unchanged from the original report's real-world damage —
`chrome_webgpu_draw_evidence.spl`'s digit-validation loops broke precisely
because "parse gives 7, not 55".

A plain `text` receiver returning its code point is separately wrong: `"A".to_i64()`
is a string-to-integer parse and should be 0/nil/error, never 65. That is a
NEW observation, not in the record above.

`s.char_at(i).to_i64()` returning **nil** is the third answer and the most
dangerous of the three: `str(nil)` renders `"nil"` and the value flows into
arithmetic without a diagnostic.

### Why this was not fixed here

Seed-side, not pure-Simple. The dispatch is in the Rust seed:
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:44,1527,1742`
(`"to_int" | "to_i64" => Some(TypeId::I64)`) routing to `rt_string_to_int`, and
`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:496,515`. There is no
`to_i64` implementation for a text receiver anywhere under `src/lib` (checked).
Out of scope for a pure-Simple bugfix lane per the fan-out guide.

### Fix direction (unchanged in spirit, sharpened)

Pick ONE contract and make all three shapes obey it. The record's own
recommendation — code point, or a hard error — still stands, and the content-
dependent switch is the part that must go. Whichever is chosen, `char_at`'s
`nil` must be eliminated in the same change, or the divergence merely moves.
The existing scanner `scripts/check/check-string-index-char-to-i64.shs` is the
right place to ratchet call sites once the contract is fixed.
