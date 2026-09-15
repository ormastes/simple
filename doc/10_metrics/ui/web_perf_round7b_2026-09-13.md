# Web-rendering perf round 7b: HTML tokenizer byte-array scan (2026-09-13)

Continuation of `doc/10_metrics/ui/web_perf_round6_2026-09-13.md`, which left
`pp_html_us` (HTML tokenize + tree build) as the largest parse-phase bucket
(1427-1544 ms summed over the 8-page catalog) and recorded a REVERTED
`.bytes()`-based candidate: it regressed because `_find_char`/`_find_substr`
called `s.bytes()` on the *whole remaining document* on every single
invocation, redecoding O(document length) repeatedly across the scan instead
of decoding once. The round-6 doc named the real fix: "threading a
document-wide byte array through the tokenizer's whole scan loop so it is
decoded once per document rather than once per `_find_char` call" — that is
exactly what this round implements.

## Fix

`src/lib/gc_async_mut/gpu/browser_engine/html_tokenizer.spl`,
`html_tokenizer_tokenize_with_limits` (main scan loop): decode
`val hb = text_to_bytes(html)` **once** at the top of the function, then
thread that same `[u8]` array through the whole scan instead of re-slicing
or re-decoding per character or per helper call:

- The outer loop's per-position dispatch (`ch == "<"`, `ch == "&"`, peeking
  `next`) now reads `hb[pos]`/`hb[pos+1]` as integer bytes instead of
  allocating a length-1 `text` via `html.slice(pos, pos+1)` on every position.
- New byte-array twins `_find_byte`, `_scan_char_data_b`, `_find_tag_close_b`,
  `_is_alpha_byte` replace the text-based `_find_char(html, ">", ...)`,
  `_scan_char_data(html, ...)`, `_find_tag_close(html, ...)`,
  `_is_alpha_char(next)` call sites inside the hot outer loop — each now
  indexes the single pre-decoded `hb` array (O(1) per probe) instead of
  allocating a new `text` slice per character compared.
- The original text-based `_find_char`/`_find_tag_close`/`_scan_char_data`/
  `_is_alpha_char` functions are kept unchanged and still used by the
  bounded, per-tag-sized call sites (`_parse_attrs`'s quoted-value search,
  raw-text `&`-scan on an already-sliced `raw_data`) where they were never
  the O(document) bottleneck.
- `_find_substr` (comment-close `-->` search) and `_find_raw_end_tag`
  (script/style/textarea end-tag search) are left as-is: comments and raw-text
  elements are rare relative to the character-data/tag-open scan this fix
  targets, and round-6 already showed `_find_raw_end_tag`-style multi-byte
  compares are not the dominant cost.

Token output is unchanged — this is a pure scan-mechanism change, no token
semantics moved.

## A/B evidence (8-page catalog, `pipeline_bench.spl`, this host)

4 alternating pairs, each running `SIMPLE_WEB_PHASE_TRACE=1` and summing
`pp_html_us` across the 8 catalog pages; Draw-IR digest is the sha256 of the
8 concatenated `[bench] digest` lines:

| pair | pp_html_us before (ms) | pp_html_us after (ms) | delta | digest before | digest after |
|---|---|---|---|---|---|
| 1 | 1363.5 | 1288.2 | -5.5% | `793b167fdefd` | `793b167fdefd` |
| 2 | 1386.3 | 1322.2 | -4.6% | `793b167fdefd` | `793b167fdefd` |
| 3 | 1432.5 | 1440.7 | +0.6% | `793b167fdefd` | `793b167fdefd` |
| 4 | 1550.0 | 1391.8 | -10.2% | `793b167fdefd` | `793b167fdefd` |

3 of 4 pairs improved (4.6-10.2%); pair 3 is flat within host-load noise (this
box was shared, same noise band as round 6's ±100 ms swing on the unmodified
baseline itself). Net direction is a real, if modest, win — not a regression,
unlike round 6's two candidates. Draw-IR digest is byte-identical (12-hex
prefix shown; full sha256 matches) across all 8 pairs both sides — the token
stream is unchanged, only the scan mechanism.

## Correctness

- `test/01_unit/browser_engine/html_tokenizer_abrupt_comment_spec.spl`: 4/4
  pass, identical both sides.
- `test/unit/browser_engine/html_tokenizer_spec.spl`: 17/17 pass, identical
  both sides.
- `test/01_unit/browser_engine/html_tokenizer_spec.spl`: 23/53 pass, 30/53
  fail on **both** the pre-change and post-change tree — confirmed
  pre-existing (baseline failure, not introduced by this change) by diffing
  the exact `✗` example list byte-for-byte between the two trees: identical.
- GPU boundary audit
  (`SIMPLE_BIN=.../simple sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs`):
  `PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1,
  submits_per_frame<=1`.

## Scope note

`sel_match`/selector matching is untouched — round 6 identified it as the
single largest style-stage leaf, but it belongs to a different lane per this
round's contract. This round is `pp_html_us` only.
