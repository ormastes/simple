# char_code_at scans are quadratic (non-ASCII), and core_string's ASCII fast path is itself O(index)

**Status:** open — measured/read baseline for the CHARACTER-alignment
campaign. Must be fixed as the Stage 1 perf prerequisite in
`doc/03_plan/language/text_index_character_alignment_inventory_2026-07-30.md`,
because character indexing multiplies the number of index→offset
translations rather than reducing it.
**Severity:** silent superlinear slowdown on text scans; no wrong
results. Two distinct defects in two different lanes.

## Defect 1 — non-ASCII `char_code_at` scans are quadratic (PROVED, measured)

Method (exact, so a later regression is detectable): candidate seed
binary sha256 `79ca755dd8e7dabf...` built from tip `d05afd1276` with
`cargo build --profile bootstrap -p simple-driver --features llvm`;
driver builds a string by repeated concatenation, then runs the standard
scan shape

```
var i = 0
while i < s.len():
    acc = acc + s.char_code_at(i)
    i = i + 1
```

timed with `/usr/bin/time -f wall=%e <binary> run bench.spl`, one process
per size. Process startup is ~0.03s and must be subtracted.

Non-ASCII payload (`"héllo中"` repeated):

| bytes | wall | minus startup |
|---|---|---|
| 2,700 | 0.04s | ~0.01s |
| 5,400 | 0.06s | ~0.03s |
| 10,800 | 0.15s | ~0.12s |

Doubling the input roughly **quadruples** the scan time — quadratic,
as expected from an O(index) translation per call.

ASCII payload (`"abcdefghij"` repeated) on the same lane:

| bytes | wall |
|---|---|
| 3,000 | 0.17s (cold) |
| 6,000 | 0.05s |
| 12,000 | 0.05s |

Flat — so the Rust seed lane has an effective O(1) ASCII path, and the
quadratic behavior is **specific to non-ASCII text** there. This refines
the standing note that "all scans are quadratic": on this lane, only
non-ASCII scans are.

## Defect 2 — `core_string.spl`'s ASCII short-circuit is O(index) (PROVED by reading)

`src/runtime/simple_core/core_string.spl:282` `rt_string_char_code_at`
(the SimpleOS / native-runtime implementation, a different lane from
Defect 1) has:

```
if index < len:
    var probe = 0
    while probe <= index and (spl_load_u8(data, probe) & 255) < 128:
        probe = probe + 1
    if probe > index:
        return spl_load_u8(data, index) & 255
```

The "fast path" itself walks from byte 0 to `index`, so it is O(index) —
meaning on this lane **even pure-ASCII scans are quadratic**, unlike the
Rust lane measured above. The general path below it also walks from byte
0. Not yet measured on hardware/QEMU; the code is unambiguous.

## Lexer baseline (for later regression detection)

Method: `<candidate binary> lex src/lib/common/json/parser.spl` (601
lines), `/usr/bin/time -f wall=%e`, warm, two consecutive runs.

Result: **0.03s, 0.03s** — stable. This is the before-number for the
alignment campaign. Every stage that touches a text primitive must
re-measure this exact command and compare; the earlier refutation of the
lexer-perf objection to character alignment is not a licence to skip the
measurement.

## Required fix direction (Stage 1 prerequisite)

Character indexing makes index→byte-offset translation the hot operation,
so it must be amortized, not repeated:

1. **Per-string byte-offset cache** — memoize the last (char_index,
   byte_offset) pair per string value and resume from it when the next
   access is at or after that index. Turns the dominant sequential-scan
   shape into O(1) amortized. Cheapest correct fix for existing call
   sites; needs a place to hang the state (the interpreter's text value,
   the runtime string header).
2. **Iterator API for hot paths** — expose a character cursor so scans
   never index by position at all. Strictly better for new code; requires
   migrating hot loops, so it complements rather than replaces (1).

An ASCII-only fast path is NOT sufficient on its own: Defect 1 shows the
non-ASCII case is where the quadratic cost lives, and Defect 2 shows a
naive ASCII probe can be quadratic itself.

## Notes

- Do not "fix" Defect 2 by deleting the probe: the general path is also
  O(index). Both need the amortization above.
- Measure before and after on BOTH lanes; they have different
  implementations and behaved differently in this baseline.

---

# Static re-audit 2026-08-01 (read-only; no timing — box under ENOSPC + high load)

All complexity below is established by READING the four implementations, not
by measurement. Four lanes exist, not two, and they disagree on both cost and
**semantics**.

## (a) The O(i) claim, confirmed per lane

| Lane | File:line | ASCII cost | non-ASCII cost |
|---|---|---|---|
| Rust seed interpreter | `src/compiler_rust/compiler/src/interpreter_method/string.rs:386-408` | O(1) amortized (memo hit) / O(n) on memo miss | **O(index)** — `s.chars().nth(idx)` at :404 walks from byte 0 |
| Hosted C runtime | `src/runtime/runtime_native.c:2303-2357` | O(1) after header flag set at :2329 | **O(index)** — decode walk :2338-2355 from `byte_index = 0` |
| Freestanding `core_string` | `src/runtime/simple_core/core_string.spl:282-323` | **O(index)** — probe :299-301 | **O(index)** — walk :304-322 from byte 0 |
| Pure-Simple interpreter | `src/compiler/10.frontend/core/interpreter/eval_methods.spl:329-341` | O(1) + 1 alloc/call | **WRONG ANSWER** — see (f) |

What makes it linear: the fallback is a from-scratch UTF-8 decode loop that
increments `byte_index` by the decoded `width` and `char_index` by 1 until
`char_index == index`. Nothing is carried between calls, so an
`i = 0..n` scan re-walks the prefix every iteration → O(n²).

**Bonus defect found while reading:** `len()` is BYTE length on every lane
(`string.rs:21`, `runtime_native.c:2126-2130`). So the canonical shape
`while i < s.len(): s.char_code_at(i)` bounds a CHARACTER index with a BYTE
count. On non-ASCII input the loop over-runs the codepoint count and the tail
iterations return 0 (the out-of-range convention) — these scans are already
subtly **wrong**, not merely slow. This is documented in-tree at
`simple_web_html_layout_renderer_foundation.spl:317-327`.

## (b) Call sites

Counts by grep over `src/` (`.spl`, invocation form `.char_code_at(`,
comment lines excluded):

- **360 invocations across 164 files** (plus 118 in `test/`).
- **120 of those sit inside a `while … .len()` loop** — i.e. 120 quadratic
  scan sites. Top files: `font_cldr_rank.spl` (12),
  `browser_engine/security/origin_policy.spl` (9),
  `simple_web_html_layout_renderer.spl` (4), `office/sheets/formula.spl` (4).
- The compiler's own lexer is **NOT** affected: it materializes
  `source.chars()` once (`src/compiler/10.frontend/core/lexer_struct.spl:167`).
  That is why the 0.03s lexer baseline above is stable and is *not* evidence
  the defect is contained.

**Worst offender by INPUT SIZE (not call count):**
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:86-96`,
`_simple_web_html_source_admitted` — `while i < html.len(): html.char_code_at(i)`
over an entire HTML payload capped at
`BROWSER_RENDERER_MAX_PAYLOAD_BYTES = 1048576` (1 MiB,
`src/lib/common/web/browser_renderer_protocol.spl:34`). On non-ASCII HTML —
i.e. essentially any real web page — that is ~5.5e11 byte-steps. It is an
**admission/DoS guard on attacker-controlled input that is itself the DoS
amplifier**. Runner-up by input size: `font_renderer.spl:1436/1457/1482/1506`
(`measure_text_width` etc.) — scans user-visible rendered text, i.e. the input
most likely to be non-ASCII, which is exactly the branch with no fast path.

## (c) Does a correct O(1) form exist today?

Yes, two, and neither is a drop-in:

1. **`byte_at`** — O(1) direct buffer read on all four lanes
   (`string.rs:409-423`, `runtime_native.c:2363+`, `core_string.spl:337`,
   `eval_methods.spl:359-365`). But it is **BYTE**-indexed. The in-tree
   comments at all four sites explicitly warn the two disagree
   (`"café,".byte_at(3) == 195` lead byte vs `char_code_at(3) == 233`).
2. **`.chars()`** — one O(n) materialization, then O(1) per element. Used by
   the lexer. Callers avoid it because it allocates N text values, which is
   unacceptable for a 1 MiB payload and pointless for an early-exit scan.

Why callers use neither: `for ch in <text>` is **broken** (corrupted loop
bindings — `for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`),
and at least 12 call sites carry a comment saying they were forced into
`char_code_at` indexing *because* of that bug. Fixing the for-loop is a
prerequisite that keeps getting worked around instead.

## (d) The ASCII probe — two different things, one helps and one is the problem

- **Helps:** `first_non_ascii` (`interpreter_method/mod.rs:22-35`) and
  `rt_str_first_non_ascii` (`runtime_native.c:~2265`) are word-at-a-time
  (`w & 0x8080808080808080`), and the *result is cached* — C in the string
  header bit `SIMD_CACHE_FLAG_IS_ASCII` (:2329), Rust in a 4-slot thread-local
  `Arc`-identity memo (`mod.rs:47-73`). That is what makes the ASCII column
  flat in the original measurement.
- **Is the problem:** `core_string.spl:299-301` walks byte-by-byte from 0 to
  `index` with **no word-at-a-time and no caching**. The file's own comment
  (:276-281) admits it stays O(index) because the header bit "lands on the
  sign bit … and is awkward to set safely from Simple". So on the freestanding
  lane even pure-ASCII scans are quadratic. It is still strictly cheaper than
  the decode walk (byte compare vs full decode), so it is a constant-factor
  win, not a regression — do not revert it.
- **Fragility in the Rust memo:** 4 slots, round-robin. A scan interleaving
  >4 live strings thrashes; on a miss `char_code_at` pays `first_non_ascii`
  **twice** (`string.rs:397` then `:400`), i.e. O(n) per call → ASCII goes
  quadratic again. Not exercised by the original 2-string benchmark.

## (e) Proposed change — NOT applied

1. **Resume cursor, all three runtime lanes.** Cache
   `(last_char_index, last_byte_offset)` next to the ASCII flag; when the
   requested index >= `last_char_index`, resume the decode walk from
   `last_byte_offset` instead of byte 0. Sequential scans → O(1) amortized;
   random access degrades to today's O(index), never worse. This is pure
   memoization of a pure function on immutable strings.
2. **`core_string`: ride the new field.** Land the cursor in a *new* header
   word so the ASCII flag can live there too, dodging the sign-bit/`reserved`
   hazard called out at `runtime_native.c:2299-2302` and
   `core_string.spl:276-281`. Also make the probe word-at-a-time (~8x).
3. **Fix the pure-Simple interpreter lane** — see (f), this is a correctness
   fix, not a perf fix.
4. **Explicitly rejected:** bulk-migrating callers to `byte_at`. That silently
   converts a character-indexed API into a byte-indexed one. It is valid ONLY
   where the caller compares against an ASCII codepoint (<128) and treats the
   index as a byte offset throughout — because no UTF-8 continuation or lead
   byte is ever < 0x80, an ASCII-literal comparison cannot false-positive
   inside a multi-byte sequence. `_simple_web_html_source_admitted` (counting
   `<` == 60) meets that bar exactly and is the single highest-value caller
   fix. The same team already did this migration deliberately elsewhere in
   that file (:356-390) — follow that precedent, do not generalise it.

**What the proposal does at a multi-byte codepoint (explicit):** the resume
cursor is advanced only by the decoder's own `width`, so it always points at a
codepoint **boundary**; resuming from it decodes exactly the codepoint a
from-zero walk would return. `char_code_at(i)` keeps returning the i-th
CODEPOINT, e.g. 233 for `"café,".char_code_at(3)`, never 195. No byte index is
ever exposed. The proposal adds **no** new byte-slicing, so the
byte-transparent-slice behaviour (`8151c391932`) is not relied on anywhere.
The one place bytes are read directly is the ASCII fast path, which by
construction has already proven every byte up to `index` is < 0x80.

## (f) NEW correctness defect — pure-Simple interpreter `char_code_at` is byte-indexed

`src/compiler/10.frontend/core/interpreter/eval_methods.spl:334-336`:

```
if idx >= 0 and idx < s.len():
    val ch = s[idx:idx + 1]
    return val_make_int(ch.char_code_at(0))
```

`s[idx:idx+1]` is **BYTE**-addressed — confirmed by the file's own comment at
:346-349 and by `8151c391932` ("byte-transparent text slices"). It slices one
byte out of a multi-byte codepoint and decodes that fragment as UTF-8, so this
lane returns garbage/0 where the seed and both compiled lanes return the
codepoint. This is the exact trap the byte-vs-char constraint warns about, and
it is already in the tree. Fix: route to `rt_string_char_code_at` — the same
extern `byte_at` already uses one branch below at :364 — which also removes a
per-call string allocation. **Untested here** (no builds permitted under
ENOSPC); flagged for verification before any fix lands.

## Verification status of this section

Read-only. Every claim above is a file:line citation, not a measurement. The
original timing tables higher in this document are unchanged and were NOT
re-run. Items needing a run once the box is healthy: (i) the >4-string memo
thrash in (d); (ii) the pure-Simple interpreter divergence in (f), which needs
a spec with a multi-byte codepoint — note that `simple test` silently
delegates to the Rust seed child, so a green run there would NOT cover lane 4.

---

# Executed verification + first caller fix 2026-08-01

Binary: `src/compiler_rust/target/bootstrap/simple` (154 MB, the canonical
LLVM-enabled seed). Everything below was RUN, not read.

**Commit-message clobber, recorded so this fix is findable:** the change below
landed as `1fc9d905bee8c44efdc285c35ce64c362a208342`, but that commit carries a
*different lane's* message (`fix(mir): make string-arm dispatch receiver-aware
for find/rfind`). A parallel session overwrote the shared scratchpad message
file between it being written and the landing script reading it. The commit's
three-file diff is this work and is correct; only the message text is wrong.
Origin had already advanced past it before the mistake was noticed, so it was
NOT rewritten. Search for the fix by path, not by commit subject.

## (g) The byte-vs-char mismatch is confirmed, and it is EXECUTABLE

Source confirmation of the (a) "bonus defect", re-checked at the cited lines:

- `src/compiler_rust/compiler/src/interpreter_method/string.rs:21`
  `"len" | "length" => Value::Int(s.len() as i64)` — Rust `String::len()`, i.e.
  BYTES. `char_count` is a *separate* method one line below (`:22`).
- `src/runtime/runtime_native.c:2125-2130` `rt_string_len` returns `s->len`
  (the byte-count header field) or `strlen`. BYTES.
- `char_code_at` is CHARACTER-indexed on both: `string.rs:404` `s.chars().nth(idx)`,
  `runtime_native.c:2338-2355` walks `char_index` against `index`.

Executed proof (`"café,"` — 6 bytes, 5 characters):

```
byte_len(len())=6
char_code_at scan bounded by len(): 0:99 1:97 2:102 3:233 4:44 5:0
byte_at      scan bounded by len(): 0:99 1:97 2:102 3:195 4:169 5:44
```

Index 5 is a **phantom character that does not exist in the string** — the
canonical `while i < s.len(): s.char_code_at(i)` shape reads it and gets 0. The
over-run is real and executable, not a reading.

**Refinement the static audit did not have:** for a predicate that only tests
`== <some ASCII code>`, the over-run does not change the *answer* — the character
indices `0..char_count-1` still cover every character, and the phantom tail
returns 0, which matches no ASCII literal. So a *counting* caller is
accidentally answer-correct. It is not correct for any caller that consumes the
returned value, or that treats the index as a position. And the phantom
iterations are the **most expensive calls in the loop**: an out-of-range index
walks the entire buffer before returning 0.

## (h) FIXED — `_simple_web_html_source_admitted` migrated to `byte_at`

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:86`.
The `<`-counting loop now uses `byte_at` with `len()` hoisted. The (e)(4)
validity argument was re-derived before relying on it and holds: the compared
literal is `<` == 60 < 128, and no UTF-8 lead byte (0xC2-0xF4) or continuation
byte (0x80-0xBF) is ever < 0x80, so byte 60 occurs exactly where the character
`<` occurs and nowhere else. Follows the precedent already set in the same file
at `text_matches_at` / `skip_wrap_spaces` / `find_from`.

Measured, non-ASCII payload (`"<p>café — naïve 中文</p>"` repeated), wall clock
per process, same binary:

| bytes | `char_code_at` | `byte_at` |
|---|---|---|
| 12,000 | 0.28s | 0.07s |
| 24,000 | 0.81s | 0.07s |
| 48,000 | **3.27s** | 0.15s |

Doubling quadruples the old form (quadratic, matching the 2026-07-30 table) and
is flat/linear for the new one. Extrapolating the quadratic to the 1 MiB
`BROWSER_RENDERER_MAX_PAYLOAD_BYTES` cap: ~21.8x more input → ~476x more work →
**~26 minutes of CPU inside the admission guard**, on attacker-controlled input,
before the renderer has parsed a single tag. That is the DoS the guard exists to
prevent.

Answer-equivalence was verified before and after on the same payloads (old and
new forms both count 800 `<` in a 12,000-byte non-ASCII document, 6 in an ASCII
document, and both reject over-limit input identically).

Regression guard added to the existing index-space spec:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl`
— `20 total, 20 passed, 0 failed`. The new block was confirmed to actually
execute by sabotaging one oracle (→ `20 total, 19 passed, 1 failed`) and
restoring it; a green `describe` is not by itself evidence the body ran.

## (i) Remaining 120 sites — the criterion, NOT a bulk sweep

A blanket `char_code_at` → `byte_at` migration is a regression generator and is
still rejected. A site is safe to migrate **only if ALL FOUR** hold:

1. The loop is bounded by `.len()` (or another byte quantity) — i.e. it is
   already in byte index space and the character probe is the odd one out.
2. Every literal the probe is compared against is **< 128**. One comparison
   against a codepoint >= 128 disqualifies the site outright, because that
   codepoint is multi-byte and can never equal a single byte.
3. The index is not passed to a CHARACTER-indexed API, and is not reported to a
   caller that will treat it as a character position. Feeding it to
   `substring`/`slice`/`index_of`/`bytes()[i]` is fine — those are byte-indexed.
4. The loop does not *consume* the probed value as a character (e.g. append it
   to a text, or pass it to something expecting a codepoint). Counting,
   comparing, and classifying against ASCII literals are fine.

Sites failing (2) or (4) need the (e)(1) resume cursor instead — that is a
runtime fix, not a caller fix, and it is still unimplemented.

Highest-value remaining candidates, in order, all **UNVERIFIED against the four
criteria** (each needs the check above run on it individually):

- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:1436,1457,1482,1506`
  (`measure_text_width` and friends) — the runner-up by input size, and the one
  most likely to see non-ASCII, since it scans user-visible rendered text.
  **Likely FAILS criterion 4** (it needs actual codepoints for glyph metrics),
  so this one probably needs the resume cursor, not `byte_at`.
- `src/lib/gc_async_mut/gpu/browser_engine/security/origin_policy.spl` (9
  invocations) — URL/origin scanning against ASCII delimiters; a plausible
  candidate for (2) and likely worth doing next.
- `src/lib/.../office/sheets/formula.spl` (4) — formula tokenizing against
  ASCII operators; plausible candidate.
- `font_cldr_rank.spl` (12) — highest raw call count but small inputs, so low
  value; and rank keys may be non-ASCII, so check (2) carefully.

## (j) `for ch in <text>` is byte-bounded AND binds a broken value — PROVED

This is the prerequisite (c) says keeps getting worked around, and it is worse
than the "corrupted loop bindings" note suggests. Executed:

```
val s = "café,"          # 6 bytes, 5 characters
for ch in s: n = n + 1; acc = acc + "<" + ch + ">"
  -> n   = 6      (BYTE count — expected 5)
  -> acc = ""     (empty: the bound `ch` contributes nothing to a concat)

for ch in s.chars(): m = m + 1
  -> m = 5        (correct)
```

So `for ch in <text>` is the **same** `len()`-is-bytes defect one level up: it
iterates the byte count while purporting to yield characters, and the value it
binds is unusable. On pure ASCII (`"abc"` → 3) it looks fine, which is why it
survives.

**Proposed clean fix (NOT applied — needs the desugar/lowering owner):** lower
`for <v> in <text-typed expr>` to `for <v> in <expr>.chars()`. `.chars()` is
already correct on every lane and is what the lexer uses
(`lexer_struct.spl:167`). That is a single lowering site rather than 120 caller
edits, it removes the reason ≥12 sites were forced onto `char_code_at`, and it
makes the idiomatic form the correct one. The cost is `.chars()`'s N-value
allocation, which is acceptable for a `for` loop (it is inherently a full
traversal) and is exactly the case where `.chars()` is the right tool — unlike
the early-exit/1 MiB scans in (i), where it is not.

Also noted while looking: `src/compiler_rust/compiler/src/interpreter_control.rs:937-995`
is a superoptimizer for precisely the `while i < s.len(): if s.char_code_at(i) == <ascii>`
shape, and it is gated on `value.is_ascii()` (`:961`). That is an additional
reason the ASCII column measured flat in the 2026-07-30 table, and it means the
ASCII half of that table is not evidence about the general path at all.

## 2026-08-01 — why these call sites exist at all

`for ch in <text>` iterates the BYTE count and binds a corrupt value on the Rust
seed JIT/MIR and native AOT paths, which is what pushed ~120 of the call sites
counted here onto the `while i < s.len(): s.char_code_at(i)` idiom in the first
place. See `for_in_text_iterates_bytes_not_chars_2026-08-01.md`.

The migration criteria in this document remain the gate for touching those call
sites. Do not start the migration until the Rust seed JIT/native lane described
in that bug is closed — `for ch in <text>` is still wrong there, so migrating a
caller off `char_code_at` today would regress it on the engine most people run.
