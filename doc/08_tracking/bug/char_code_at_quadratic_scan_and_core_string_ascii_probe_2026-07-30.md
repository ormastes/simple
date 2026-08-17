# char_code_at scans are quadratic (non-ASCII), and core_string's ASCII fast path is itself O(index)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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
| Pure-Simple interpreter | `.../interpreter/_EvalOps/access_literal_assign_eval.spl:78-84` (was cited as `eval_methods.spl:329-341`, dead code — see audit note) | O(1) + 1 alloc/call | **WRONG ANSWER** — see (f) |

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
   ~~`eval_methods.spl:359-365`~~ → `_EvalOps/access_literal_assign_eval.spl:101-107`).
   But it is **BYTE**-indexed. The in-tree comments at all four sites explicitly
   warn the two disagree (`"café,".byte_at(3) == 195` lead byte vs
   `char_code_at(3) == 233`).

   > **NOW-WRONG as originally written (audited 2026-08-01).** "O(1) direct
   > buffer read on **all four** lanes" was **false for the pure-Simple
   > interpreter lane on 2026-07-30**. The `byte_at` arm cited here lived only
   > in `eval_methods.spl`, which was a **dead duplicate** shadowed by the
   > package-local `_EvalOps` copy (sabotage-proven both directions) and was
   > deleted in `f97dfbbb8ee`. The live text-method table had **no `byte_at`
   > arm at all**, so `s.byte_at(i)` under the pure-Simple interpreter fell
   > through to `eval_set_error` and returned `-1`/`VAL_NONE` — silently, since
   > a missing arm does not fail at the call site. It became true only when
   > `f97dfbbb8ee` added the arm to the live file. **Consequence for this
   > document's recommendation:** "use `byte_at` instead of `char_code_at` to
   > escape the quadratic scan" was **not viable on the interpreter lane** at
   > the time it was written, and is viable only from `f97dfbbb8ee` forward.
   > The recommendation for the other three lanes is unaffected.
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

~~`src/compiler/10.frontend/core/interpreter/eval_methods.spl:334-336`~~ (dead
duplicate — see audit note below):

```
if idx >= 0 and idx < s.len():
    val ch = s[idx:idx + 1]
    return val_make_int(ch.char_code_at(0))
```

> **CONTAMINATED evidence, but the verdict SURVIVES (audited 2026-08-01).**
> The snippet above was read from `eval_methods.spl`, a dead duplicate deleted
> in `f97dfbbb8ee`. Re-derived against the copy that actually ran
> (`_EvalOps/access_literal_assign_eval.spl`): it had the **same defect in a
> different shape** — `val ch = s.substring(idx, idx + 1)` then
> `ch.char_code_at(0)`, likewise byte-addressed. So "(f) pure-Simple
> interpreter `char_code_at` is byte-indexed" **still holds**; only the quoted
> source line was from the wrong file. Both copies were subsequently repaired
> to delegate straight to `s.char_code_at(idx)`; the live arm is now
> `_EvalOps/access_literal_assign_eval.spl:78-84`. Full history:
> `doc/08_tracking/bug/2026-08-01_interpreter_char_code_at_byte_indexed.md`
> and
> `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

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

## Re-verification 2026-08-07 — still open, no lane changed since 2026-08-01

Executed + read-only re-check of all four lanes ahead of a fresh perf sweep.
**Verdict: the suspected-stale defect is NOT stale — it is still live**, and
none of the four lane implementations have changed since the 2026-08-01
audit above. No fix was applied in this pass: the lane that is measurable
(the Rust seed) is off-limits under the standing "fix .spl, not Rust" rule,
and the two lanes that ARE `.spl`/fixable (`core_string.spl`'s probe, the
freestanding walk) require a bootstrap rebuild to verify any change, which
this task's constraints forbid. So this pass is measurement + doc update
only, matching the "already tracked, not yet fixed" outcome the rest of this
file already documents.

**Binary identity (do not read these numbers as continuous with the tables
above — different binary):** `bin/release/x86_64-unknown-linux-gnu/simple`,
58,804,688 bytes, mtime 2026-08-07 04:52 UTC. `bin/simple run <file>` on this
binary prints `WARNING: this Rust-built Simple binary is a bootstrap seed
only...` / `Build and use the pure-Simple bin/simple instead.` to stderr and
then executes anyway — so despite the "pure-Simple self-hosted binary is the
default tool" rule, this deployed `bin/simple` currently falls back to the
Rust seed interpreter (`interpreter_method/string.rs`) for `run`. The earlier
tables in this file used a different binary
(`src/compiler_rust/target/bootstrap/simple`, 154 MB); today's numbers are
from the deployed symlink target instead. Loop shape matches the original
methodology exactly: `while i < s.len(): acc = acc + s.char_code_at(i); i += 1`
(byte-bounded, so on non-ASCII input a fraction of iterations are the phantom
out-of-range indices from (g) above — the most expensive iterations, per that
section — this is deliberate, for comparability with the original table, not
the cost of a "correct" character-bounded scan).

Non-ASCII payload (`"héllo中"` repeated), `/usr/bin/time -f wall=%e bin/simple
run <file>`, one process per size:

| chars (approx bytes) | wall |
|---|---|
| 6,250 | 0.03s |
| 12,500 | 0.04s |
| 25,000 | 0.10s |
| 50,000 | 0.31s |
| 100,000 | 1.50s |

12,500→100,000 is 8x the input and **37.5x** the time — clearly superlinear,
consistent with the O(index) `.chars().nth(idx)` walk at `string.rs:404`
(now-current line, re-grepped, unchanged) and matching the original
2026-07-30 table's quadratic shape (there: 2,700→10,800 bytes was 4x input,
~4x-plus time after subtracting the ~0.03s startup floor).

ASCII payload (`"abcdefghij"` repeated) — extended to sizes well above the
~0.02-0.03s process-startup floor, since the original 25k/50k pair (both
0.02s) sits inside that floor and cannot distinguish O(1)-amortized from
linear:

| chars | wall |
|---|---|
| 25,000 | 0.02s |
| 50,000 | 0.02s |
| 400,000 | 0.05s |
| 1,000,000 | 0.10s |

400,000→1,000,000 is 2.5x the input for 2x the time (sub-linear to linear,
well below quadratic) — confirms the ASCII memo (`first_non_ascii` cached via
the 4-slot thread-local in `mod.rs`) is still doing its job on this lane; the
25k/50k pair alone would have been insufficient evidence (both inside the
startup floor).

**Per-lane status, re-read (not re-executed except the Rust seed above)
against the (a) table in the 2026-08-01 section:**

| Lane | File:line (re-checked 2026-08-07) | Status |
|---|---|---|
| Rust seed interpreter | `src/compiler_rust/compiler/src/interpreter_method/string.rs:404` (`.chars().nth(idx)`) | **Unchanged — confirmed live by execution above.** |
| Hosted C runtime | `src/runtime/runtime_native.c:2423-2477` (`rt_string_char_code_at`) | **Unchanged** — ASCII path still O(1) via `SIMD_CACHE_FLAG_IS_ASCII` (checked/set at :2442-2450), non-ASCII still an O(index) walk from `byte_index = 0` at :2458. Same shape as cited 2026-08-01. Not re-executed (no bootstrap rebuild permitted this pass). |
| Freestanding `core_string` | `src/runtime/simple_core/core_string.spl:282-330` (`rt_string_char_code_at`) | **Unchanged.** The ASCII probe at (current) lines ~299-301 still walks byte 0→`index` with no word-at-a-time and no cache — same in-file comment (lines 288-294) still explains the sign-bit/`reserved`-field obstacle as unresolved. General non-ASCII path still walks from byte 0 too. Not re-executed. |
| Pure-Simple interpreter | `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:78-84` | **Correctness fix from (f) still in place** (delegates straight to `s.char_code_at(idx)`, no byte-slice-then-decode), so it now shares whatever complexity the runtime it's linked against has — same O(index) non-ASCII cost as the C/freestanding lanes when run compiled, or the Rust seed's cost when run interpreted. Not independently re-executed this pass. |

**Why no fix was applied here:** the only lane this task could execute
(the Rust seed, via `bin/simple run`'s seed fallback) is explicitly off the
"fix .spl, not Rust" boundary. The two lanes that are legitimately fixable
in `.spl` — `core_string.spl`'s ASCII probe and the freestanding decode walk,
per the resume-cursor proposal in (e) above — cannot have a fix *verified*
without a bootstrap rebuild, which this task's constraints explicitly forbid.
Applying an unverified change to a shared runtime file in a shared working
tree was judged higher-risk than leaving the well-documented status quo, so
this pass is limited to confirming today's numbers and refreshing the
per-lane table above. The (e) resume-cursor fix — cache `(last_char_index,
last_byte_offset)` and resume the decode from there when the next index is
at or beyond it — remains the correct, still-unimplemented direction.

No new spec was added: a timing-ratio regression guard at these input sizes
sits inside a ~0.02-0.03s process-startup floor for the smaller cases and
would be flaky; the existing answer-equivalence spec at
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_scan_index_space_spec.spl`
(from the (h) fix) already locks in correctness for the one caller site that
was migrated off `char_code_at`.

## 2026-08-01 — why these call sites exist at all

`for ch in <text>` iterates the BYTE count and binds a corrupt value on the Rust
seed JIT/MIR and native AOT paths, which is what pushed ~120 of the call sites
counted here onto the `while i < s.len(): s.char_code_at(i)` idiom in the first
place. See `for_in_text_iterates_bytes_not_chars_2026-08-01.md`.

The migration criteria in this document remain the gate for touching those call
sites. Do not start the migration until the Rust seed JIT/native lane described
in that bug is closed — `for ch in <text>` is still wrong there, so migrating a
caller off `char_code_at` today would regress it on the engine most people run.

## 2026-08-08 — re-verify + reachability probe for the `.spl` lane

**Load caveat:** host `uptime` load average was ~21-22 on 32 cores for the
entire session (concurrent native-builds). Absolute wall times below are
therefore inflated and noisy; conclusions rest on **ratios within the same
run**, which are much more robust to contention than absolute numbers — a
loaded host multiplies both arms of a comparison, it does not manufacture
growth in one arm while leaving the other flat.

### Scaling re-measurement (clean method: doubling string construction)

Original method (`bench_nonascii.spl`, build-by-repeated-concat) was
discarded after noticing the construction loop itself is `s = s + unit`
repeated N times — an *independent* O(n²) cost that confounds the
`char_code_at` measurement. Replaced with `s = s + s` doubling (O(n) total
construction cost), isolating the scan loop as the dominant cost at scale.
`bin/simple run <probe>.spl`, `/usr/bin/time -f wall=%e`, one process per
size, non-ASCII payload `"héllo中"`, ASCII payload `"abcdefghij"`:

| doublings | non-ASCII bytes | non-ASCII wall | ASCII bytes | ASCII wall |
|---|---|---|---|---|
| 12 | ~84.7M "chars" scanned (string ~1.2MB) | 0.09s | ~4.2MB | 0.03s |
| 13 | (2x) | 0.50s (~5.5x) | (2x) | 0.02s |
| 14 | (4x from d=12) | 1.47s (~2.9x from d=13) | (4x) | 0.04s |
| 15 | (8x from d=12) | 6.62s (~4.5x from d=14) | (8x) | 0.03s |

Non-ASCII: each size doubling costs roughly 3-5.5x wall time (quadratic
predicts ~4x) — **quadratic scaling reconfirmed**, consistent with the
2026-08-07 finding. ASCII: flat at 0.02-0.04s across an 8x size range —
**ASCII memoization still holds**. Because ASCII stayed flat across the same
loaded window that non-ASCII grew ~280x (0.09s→6.62s doubled 3x = 8x size),
the growth cannot be attributed to load alone.

Probe files (kept for reproduction, not committed):
`/tmp/claude-1000/.../scratchpad/bench2_nonascii_{12,13,14,15}.spl` and
`bench2_ascii_{12,13,14,15}.spl` (doubling construction + scan loop).

### Per-lane provenance (file:line), established empirically this pass

- **Rust seed interpreter** (`SIMPLE_EXECUTION_MODE=interpret`):
  `src/compiler_rust/compiler/src/interpreter_method/string.rs:441-464`
  (`"char_code_at" =>` arm). This file **already carries** an ASCII-prefix
  short-circuit (`first_non_ascii(bytes) > idx`) with `shared_text_is_ascii`
  memoization — the 2026-07-30 doc's line/behavior citation (`:404`,
  `.chars().nth(idx)` unconditionally) is now stale; `.chars().nth(idx)` is
  only reached as the **fallback** once the index is past the ASCII prefix.
  Interpret-mode d=14 non-ASCII probe: 1.85s (vs default-mode 1.24s at the
  same size — see below).
- **JIT / native AOT** (`bin/simple run` default, and `native-build`):
  MIR/LLVM/Cranelift lowering (`src/compiler_rust/compiler/src/codegen/**`,
  e.g. `codegen/llvm/functions/calls.rs:1941`,
  `codegen/instr/closures_structs.rs:1528`) all lower `.char_code_at(i)` to a
  call to the C symbol `rt_string_char_code_at`, defined at
  `src/runtime/runtime_native.c:2423-2477`. That C implementation now also
  carries the same ASCII-prefix short-circuit (`SIMD_CACHE_FLAG_IS_ASCII`
  cache + `rt_str_first_non_ascii` prefix scan at :2440-2450) with a full
  O(index) walk as fallback at :2456-2472 — this is what's actually linked
  into `libsimple_runtime.a` (confirmed via `nm bin/release/.../libsimple_runtime.a
  | grep rt_string_char_code_at` → defined, `T` in the `.a`'s C-compiled
  object). Default-mode d=14 non-ASCII probe: 1.24s, same order of magnitude
  as interpret-mode (1.85s) — both fall back to the walk for this payload,
  as expected since `"héllo中"` has non-ASCII bytes early in every repeat
  unit, so no call in the loop stays inside a growing ASCII prefix.
  Also note: `src/compiler_rust/runtime/src/value/collections.rs:3443-3477`
  has an **independent third copy** of this exact ASCII-prefix logic in the
  runtime *crate* (Rust, not C) — not confirmed which lane actually calls
  this one vs the C one; recorded for completeness, not exercised directly.
- **Freestanding `core_string.spl`** (SimpleOS / `--runtime-bundle=simple-core`
  native-build lane): `src/runtime/simple_core/core_string.spl:296-330`. This
  file **also already has the same ASCII-prefix idea** but, unlike the C/Rust
  lanes, the probe loop itself (`while probe <= index and ...: probe += 1`
  at :309-311) is **still O(index) per call even for pure ASCII** because
  there is no per-string memoization — the in-file comment (:288-295)
  explicitly says so: "this freestanding lane does NOT cache the all-ASCII
  result in the string header... stays O(index) per call rather than
  becoming O(1)... Filed as follow-up." This is Defect 2, still open, and is
  the smaller of the two residual issues (still linear per full scan, not
  quadratic, since the probe re-derives ASCII-ness on every call rather than
  caching it — but it is a repeated O(index) probe, which is wasted work the
  hosted lanes no longer pay).

### Is the `.spl` lane reachable/verifiable without a bootstrap rebuild? — NO, empirically

Landed an unconditional marker (`rt_stderr_write("MARKER_CCA_SPL_LANE_LIVE\n")`
as the first line of `rt_string_char_code_at` in `core_string.spl`) and ran:

```
bin/simple native-build <probe>.spl -o <bin> --runtime-bundle=simple-core
```

Build succeeded (exit 0) and the resulting binary ran and printed the
correct answer (20013, the codepoint for 中), but the marker **never
appeared** in stdout/stderr, and — decisively — the marker string is **absent
from the binary entirely**: `strings -n 3 <bin> | grep MARKER` found nothing,
while a positive control (`strings -n 3 <bin> | grep abc`, the ASCII test
literal from the same source file) **did** find the literal, so the
string-detection method itself works and the absence is real, not a
false negative. `nm` confirms a `T rt_string_char_code_at` symbol is defined
in the binary — i.e. *some* implementation got linked — just not the edited
`.spl` one. `--runtime-bundle=simple-core` did not cause the freshly-edited
`core_string.spl` to be recompiled and linked; `find_simple_core_runtime_library()`
(`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:479-506`)
looks for a **prebuilt** `<exe_dir>/simple-core/libsimple_runtime.a` (or
`$SIMPLE_SIMPLE_CORE_PATH`), neither of which existed near
`bin/release/x86_64-unknown-linux-gnu/`, so the build silently fell back to
a different runtime lane instead of failing loud.

Attempted the documented rebuild path
(`doc/08_tracking/bug/simple_core_pure_simple_archive_builder.md`,
`scripts/check/check-simple-core-runtime-smoke.shs`): building even a single
source file from the tree as a standalone archive part —
`bin/simple native-build --source src/runtime/simple_core --entry-closure
--entry src/runtime/simple_core/core_string.spl --no-mangle --emit-archive
--output ... --clean` — pulled in and started compiling the **entire
compiler codebase** (SFFI, backend, driver modules — visible from
cross-module symbol-collision warnings for `compile_native`,
`compiler_infer_types`, `dir_remove_all`, etc., none of which belong to
`core_string.spl`), and did not finish inside a 300s timeout. This is
consistent with the `.spl` lane needing a bootstrap-rebuild-scale operation
to verify, matching this doc's original 2026-07-30 scope decision.

**Verdict: the `.spl` lane (`core_string.spl`) is NOT reachable/verifiable
today without a costly (bootstrap-scale, >5 min, likely >20 min given 18
source files and current host load) rebuild.** No fix was applied to
`core_string.spl` this pass (the marker was landed, confirmed absent from
every build artifact produced, then removed — verified removed via
`/usr/bin/grep -n MARKER_CCA src/runtime/simple_core/core_string.spl`,
exit 1, no match).

**Unblock condition:** either (a) a prebuilt, ABI-complete
`libsimple_runtime.a` built from `src/runtime/simple_core/*.spl` exists at
`<exe_dir>/simple-core/libsimple_runtime.a` or is pointed at via
`SIMPLE_SIMPLE_CORE_PATH`/`SIMPLE_CORE_RUNTIME_PATH`, freshly rebuilt after
any `.spl` edit (i.e. `scripts/check/check-simple-core-runtime-smoke.shs`
run to completion, currently untimed but bounded well past this task's
budget), or (b) the self-hosted `70.backend` native-build linker path
(which is what `bin/simple native-build` actually dispatches to — a
separate, pure-Simple reimplementation of the Rust `native_project`
config/linking logic examined above, not confirmed to share its runtime-bundle
selection logic) is confirmed to pick up a freshly-built simple-core archive.
Neither was exercised to completion this pass; both are out of scope for a
non-bootstrap task.

### Fix status

No source fix applied. The standard remedy (index→byte-offset cursor
memoized per string, replacing the O(index) probe/walk on every call) remains
correct and unimplemented in all three lanes for the full non-ASCII case, and
additionally unimplemented for the ASCII case specifically in
`core_string.spl` (Defect 2). Per the reachability finding above, only the
`core_string.spl` copy is a legitimate `.spl`-only fix; the C
(`runtime_native.c`) and interpreter (`string.rs`) copies are out of the
"fix .spl, not Rust" scope by policy, and the Rust runtime crate copy
(`collections.rs:3443`) is likewise Rust.

### Fence — not added

Per the existing 2026-08-07 rationale (still valid): a non-ASCII scaling-ratio
assertion would be asserting a known-open defect (a red fence is worse than
none), and a fence on the ASCII arm's flatness was considered but not added
this pass — it would need to be proven stable across at least two runs under
present load before landing, which was not done given the time already spent
on the reachability probe above. Left as a follow-up, not fabricated.

## 2026-08-08 (later pass) — independent re-confirmation, no fix applied, second blocker found

Assigned to re-attempt the `.spl`-lane fix from scratch. Before touching
anything, re-checked the state left by the reachability-probe pass directly
above (same date): `/usr/bin/grep -n "MARKER_CCA"
src/runtime/simple_core/core_string.spl` → no match (marker confirmed
removed), and the live `rt_string_char_code_at` body
(`src/runtime/simple_core/core_string.spl:296-330`) was read in full and
matches this doc's citation exactly — ASCII probe still `while probe <=
index and (spl_load_u8(data, probe) & 255) < 128: probe += 1` (byte-0 walk,
no cache), same "awkward to set safely from Simple" comment at :288-295,
general decode walk still starts `byte_index = 0`. No partial fix was left
on disk. Host load this pass: `70.96, 61.66, 46.14` (1/5/15-min) — over 3x
the ~21-22 load the reachability probe ran under, reinforcing that the
bootstrap-scale verification path (`>5min, likely >20min` per that pass)
was, if anything, further out of budget, not closer.

**Conclusion: same verdict independently reached — do not blind-edit.** The
`.spl` lane cannot be verified without a bootstrap-scale rebuild
(`--runtime-bundle=simple-core` links a prebuilt archive, not the edited
source; the standalone single-file archive build pulls in the entire
compiler and does not finish in 300s), and that path is out of scope here.

**Second, independent blocker found while re-deriving the fix design (not
previously stated as a *structural* blocker in this doc — worth recording
even though no rebuild was attempted to confirm it empirically):** the
resume-cursor remedy in (e) requires a place to persist per-string mutable
state (`last_char_index`, `last_byte_offset`) across calls. In this lane
there is no safe home for it even before the verification problem:

- The header bit the hosted C/Rust lanes use for their ASCII-cache flag is
  bit 31 of the `reserved` field, which lands on the sign bit of the i64
  header word at offset 0 — already documented in-file (:288-295) as
  "awkward to set safely from Simple," and the same obstacle blocks storing
  a byte-offset cursor there too (a cursor needs more than 1 bit, so it's
  strictly harder than the flag that was already rejected).
- The only alternative, a module-level pointer-keyed memo (mirroring the
  Rust seed's 4-slot thread-local `Arc`-identity memo), is foreclosed by a
  standing repo defect: `Dict` is broken under native codegen (`.len()`
  always returns -1, `.get()` on a struct/enum/non-scalar value is
  corrupt/segfaulting) — see `.claude/rules/code-style.md` "Native-Codegen
  Dict Pitfalls" and `doc/07_guide/language/dict_native_pitfalls.md` — and
  native codegen is exactly the lane `core_string.spl` compiles into.

So the remedy this doc has specified since 2026-07-30 needs a **new header
word** added to the string layout (to host both the ASCII flag and the
cursor, sidestepping the sign-bit hazard) before it is landable as a
`.spl`-only change here at all — a prerequisite independent of, and prior
to, the verification blocker. This is the concrete unblock condition to add
alongside the existing one: (a) a prebuilt, freshly-rebuilt
`libsimple_runtime.a` reachable for verification, **and** (b) a string
header layout change to hold the per-string cursor.

Also confirmed explicitly, since a narrower fix is tempting when a full one
is blocked: word-at-a-time-ing the existing ASCII probe (a stateless,
purely-local change, ~8x on the probe's own constant factor per (e)(2))
remains available and safe to land independently, but per this task's own
framing it is **not a fix** — it does not touch the non-ASCII decode walk,
which is where the quadratic behavior actually lives (Defect 1's O(index)
cost class is unchanged by a faster O(index) probe). Not applied, to avoid
it being mistaken for progress on the tracked defect.

The other `.spl` site, `_EvalOps/access_literal_assign_eval.spl:78-84`, was
also re-checked: it still delegates straight to `s.char_code_at(idx)` (the
(f) correctness fix from 2026-08-01 remains in place) and carries no
independent scan of its own to fix — it simply inherits whichever runtime
lane it is linked/interpreted against.

No source edit was made this pass; nothing was reverted (there was nothing
to revert).

## 2026-08-17 verification — runtime lane

**Verdict: STILL OPEN, confirmed by source. Correctness is fine; only cost is wrong.**

`src/runtime/simple_core/core_string.spl:296-337` (`rt_string_char_code_at`)
confirms the doc. The ASCII short-circuit at `:312-317` scans `probe` from 0 up
to `index` on every call, so the "fast path" is itself O(index) and a loop over
a string is O(n^2). The freestanding lane's own comment at `:290-295` states
this explicitly:

> "this freestanding lane does NOT cache the all-ASCII result in the string
> header, so it stays O(index) per call rather than becoming O(1). The header bit
> the hosted runtimes use is bit 31 of the `reserved` field, which lands on the
> sign bit of the i64 word at offset 0 and is awkward to set safely from Simple."

Not attempted here: the O(1) form needs the all-ASCII header bit to be settable
from Simple, which is the same i64-sign-bit obstacle the comment names. That is a
real design task, not a local edit, and no measurement was taken to size the win.

**What was NOT proven.** No timing was re-measured this session (the host was
running a bootstrap at ~98% CPU, so any timing taken now would be noise). This
verification is a source-shape confirmation only.

## 2026-08-17 verification — runtime slice (classified by CONTENT)

**Verdict: STILL OPEN — refuted by source, and the source says so itself.**
`src/runtime/simple_core/core_string.spl:283-295`, the comment block immediately
above `rt_string_char_code_at` (:296), states the remaining defect verbatim:

> NOTE: unlike the hosted C/Rust runtimes, this freestanding lane does NOT cache
> the all-ASCII result in the string header, so it stays O(index) per call rather
> than becoming O(1). The header bit the hosted runtimes use is bit 31 of the
> `reserved` field, which lands on the sign bit of the i64 word at offset 0 and
> is awkward to set safely from Simple.

So the ASCII fast path is a plain byte compare instead of a full UTF-8 decode (a
constant-factor win, matching the doc's FIXED sub-item (h)), but the per-call
O(index) scan — the quadratic term when a caller walks a string — is unfixed.

**What was NOT proven.** No timing re-measurement. The quadratic *magnitude* in
the doc's baseline table is unre-run; only the code shape was verified.
