# Design: fixing `char_code_at`'s residual O(N²) scan (no implementation, analysis only)

Status: DESIGN ONLY — not implemented. Written in response to a request to
design (not land) the fix for the quadratic-scan defect blocking the
`web x headless` showcase cell (the other blocker, a JIT gap where a
module-level `val` with a function-call initializer never runs, is out of
scope here).

Every claim below is labeled **PROVED** (read directly from source/git at
`HEAD=852a32c14bf`, current `main`) or **INFERRED** (reasoned from code
shape, not executed/measured — this task explicitly forbids builds/benchmarks).

## 1. Locate the primitive — four implementations, not three

The brief assumed three engines (interpreter / JIT / native runtime). Reading
the code turns up **four independent implementations**, and — important,
non-obvious finding — **three of them were already patched on 2026-07-28**,
same-day as (and possibly predating) the "still-unfixed" memory note this
task was briefed from.

### 1a. Native runtime C (`src/runtime/runtime_native.c:2303`) — FIXED 2026-07-28

```c
int64_t rt_string_char_code_at(int64_t string, int64_t index) {
    ...
    if ((uint64_t)index >= len) { ... }
    else if (s && (s->reserved & SIMD_CACHE_FLAG_IS_ASCII)) {
        return data[index];                       // O(1)
    } else {
        uint64_t first_hi = rt_str_first_non_ascii(data, len);
        if (first_hi == len) {                     // whole string ASCII
            if (s) s->reserved |= SIMD_CACHE_FLAG_IS_ASCII;   // cache forever
            return data[index];                     // O(1)
        }
        if (first_hi > (uint64_t)index) {           // idx inside ASCII prefix
            return data[index];                     // O(1)
        }
        /* fall through to the walk below */
    }
    while (byte_index < len) { ... }                 // O(index) UTF-8 walk
```

Does it restart from byte 0? **Only conditionally now.** Whole-ASCII strings
(flag cached on the string header's `reserved` field, bit `SIMD_CACHE_FLAG_IS_ASCII`)
are O(1) forever after the first call. Any index that falls **at or after**
the first non-ASCII byte still falls through to the original byte-0 UTF-8
walk, unchanged. PROVED via `git log -1 -S"rt_str_first_non_ascii" -- src/runtime/runtime_native.c` → commit `4fb66c9678d`, `perf(runtime): make char_code_at O(1) on ASCII instead of O(i) in all engines`, landed 2026-07-28, and it is an ancestor of current `HEAD`.

### 1b/1c. Rust seed's shared runtime lib (`compiler_rust/runtime/src/value/collections.rs:2268`) and tree-walk interpreter (`compiler_rust/compiler/src/interpreter_method/{mod.rs,string.rs}`) — FIXED, same commit

`collections.rs::rt_string_char_code_at` is a byte-for-byte port of 1a onto
the Rust-seed's own `RtCoreString` header (also a 32-bit `reserved` bitfield,
same `RT_STRING_FLAG_ASCII` bit, same fallback shape). This is the function
JIT-compiled and native-compiled Simple code calls via `extern "C"`.

The Rust seed's **tree-walking interpreter** (used when the seed runs a
program without JIT/native compilation) can't reuse a header bit — its
strings are `Arc<String>`, no spare bits — so it uses a **4-slot
thread-local memo keyed on `Arc::ptr_eq`** instead (`interpreter_method/mod.rs:37-73`,
`shared_text_is_ascii`). Same three-way branch (cached-ASCII / whole-string-ASCII / inside-ASCII-prefix / fall through to `s.chars().nth(idx)`), same residual: **any non-ASCII byte before the query index still triggers the full O(idx) walk, on every call**, because the memo only records a boolean, not a position.

### 1d. Self-hosted pure-Simple interpreter — NOT part of the Jul-28 fix, and structurally different

`src/compiler/10.frontend/core/interpreter/eval_methods.spl:329-341` (and a
near-duplicate at `_EvalOps/access_literal_assign_eval.spl:34-45` — two
copies of the same method, a separate finding worth flagging: they can and
already have drifted independently):

```
if method_name == "char_code_at":
    if arg_eids.len() > 0:
        val idx_val = eval_expr(arg_eids[0])
        val idx = val_get_int(idx_val)
        if idx >= 0 and idx < s.len():
            val ch = s[idx:idx + 1]
            return val_make_int(ch.char_code_at(0))
        return val_make_int(0)
```

This does **not** walk from byte 0 the way the brief assumed. `s[idx:idx+1]`
lowers to `rt_slice` (`runtime_native.c:3067`), whose string branch (line
3098-3127) does `s->data + begin` directly — a **byte-offset**, O(1) (plus an
O(1) one-byte copy) operation, PROVED by reading `rt_slice`. So this
implementation is **fast (O(1) per call) but silently wrong on non-ASCII
text**: it treats the character index `idx` as if it were a byte offset. On
a string with a multi-byte codepoint before `idx`, `s[idx:idx+1]` slices a
byte out of the middle of a different codepoint than the caller asked for,
and `.char_code_at(0)` on that 1-byte fragment decodes garbage (this is
exactly the bug the neighboring `byte_at` comment in the same file
describes for the *reverse* confusion). **This is a correctness bug, not a
perf bug** — but it means "all three/four engines walk from byte 0" is not
accurate for this engine either; it has its own, different defect.

**Open question requiring a measurement, not guessed here (see §5):** which
of these four implementations does the showcase's actual failing render
path invoke, and does the deployed/tested binary predate or postdate
`4fb66c9678d`? That determines whether this defect is still live for that
specific run.

## 2. Blast radius

**PROVED** (raw grep, deduped for the `src/std -> src/lib` symlink per the
stated trap, excluding vendor and `.pre-erp` backups):
- `git grep -c "char_code_at"` → **481 occurrences across 188 files**
  (includes defs, comments, non-loop lookups).
- Restricted to actual `.spl` call sites (`.char_code_at(`, excluding the
  four engine-internal `.rs`/`.c`/`.h` implementations above): **343 call
  sites**.

**INFERRED / heuristic** (grep for `while`/`for` within 10 source lines
above each call site — a coarse over-approximation, not a per-site audit):
**278 of the 343** sit in a window that contains a loop keyword. This is an
upper bound, not a verified count — some of those loops iterate over
something other than the same string's index (e.g. a `for` over an
unrelated list two lines above a single lookup), and the true "scans this
string's index space in a loop" count is smaller. A precise count needs
per-site triage, which this reading-only task did not do for all 278.

**One concretely confirmed, still-unconverted hot loop, directly in the
showcase's own code path** (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:86-97`):

```
fn _simple_web_html_source_admitted(html: text, byte_limit: i64) -> bool:
    if html.len() > byte_limit:
        return false
    var part_count = 1
    var i = 0
    while i < html.len():
        if html.char_code_at(i) == 60:      # '<'
            part_count = part_count + 1
            ...
        i = i + 1
    true
```

This is an admission gate that runs over the **entire HTML payload** before
parsing starts, on every render. Notably, comments at lines 317-390 of the
*same file* say "Do NOT reintroduce `char_code_at`/`char_at` here" and
describe migrating sibling scanners in this file to byte-indexed access for
exactly this reason — this one call site was missed by that migration.

## 3. Design of the fix — recommendation

Four candidates were posed. Recommendation: **(b) as the default, zero-migration
fix for all 343 existing call sites, plus (a) as a new opt-in idiom for new/hot
code** — not a single winner-take-all choice. Reasoning follows.

### Why not header-bit caching (the mechanism 1a/1b already use)

The obvious extension of the landed fix is: instead of caching one bit
("is this string all-ASCII"), cache a `(last_char_index, last_byte_offset)`
pair on the string value, so a monotonic forward scan is O(1) per step from
wherever it left off. This is the natural continuation of 1a/1b's own
pattern — but their header has no room for it. `RtCoreString.reserved` is a
**single 32-bit field**, already double-booked: bit 0 is `RT_CORE_STRING_FLAG_SHARED`
(interning), bit 1 is the new ASCII flag, and bits `[29:0]` are reserved for a
future codepoint-count cache with a documented hazard already written into the
code ("writing a cp-count would clear the SHARED bit"). Adding a full
`(index, offset)` pair means growing the struct — extra bytes on **every**
string allocation across two independent C-ABI-compatible struct definitions
(`runtime_native.c`'s `RtCoreString` and `collections.rs`'s Rust mirror of
it) that must stay bit-for-bit in sync. That's an invasive, cross-engine ABI
change for a perf cache, not the same "reuse the existing spare bit" move
the Jul-28 fix made.

### Recommendation: side-table cursor cache (extends 1c's proven pattern), not a header change

The Rust tree-walk interpreter (1c) **already solved this without touching
the header**: a bounded thread-local memo keyed on pointer/Arc identity
(`ASCII_MEMO`, 4 round-robin slots). Extend that same mechanism, in all
three of the "correct" engines, from `bool` to `(char_index: u64, byte_offset: u64)`:

- **On a call with `idx == cached_index + 1`** (the overwhelmingly common
  shape — a `while i < s.len(): ... char_code_at(i) ...` forward scan):
  resume the UTF-8 decode from `cached_byte_offset`, O(1) amortized per
  call, O(N) total over a full scan.
- **On any other `idx`** (random access, a decreasing index, or a cache
  miss): fall back to exactly the existing behavior — walk from 0 (or from
  the ASCII-prefix fast path already in place), and refresh the cache slot.
  No input regresses versus today; worst case is unchanged.
- Same soundness argument the Jul-28 fix already established and documented:
  Simple strings are immutable, so a cache entry keyed on allocation
  identity never goes stale; a miss only costs a rescan, never a wrong
  answer.
- **Source-compatible: zero caller changes.** All 343 existing call sites,
  including the ones this reading pass didn't individually audit, get the
  amortized-O(1) behavior for free, with no migration risk. This matters
  given the 278-heuristic count above is explicitly not a verified
  per-site list — a caller-transparent fix doesn't need that list to be
  complete.
- For the C/native-runtime and Rust-seed-runtime engines (1a/1b), implement
  the equivalent memo as a small **fixed-size side table** (thread-local or
  per-render-context, same round-robin-eviction shape as 1c), not a header
  field — sidesteps the struct-growth/ABI problem entirely and reuses code
  the Rust interpreter side already has, ported to C.
- For the self-hosted interpreter (1d): this is also where its *correctness*
  bug should be fixed, by routing `char_code_at` through the same
  generalized runtime primitive the other three engines use (`rt_string_char_code_at`,
  now cursor-cached) instead of its own `s[idx:idx+1]` byte-slicing
  shortcut. This closes both the correctness gap (non-ASCII text) and
  unifies four independently-drifting implementations of the same method
  into one canonical, single-source-of-truth decode+cache, which is worth
  doing on its own merits — the Jul-28 fix already shows what happens when
  "fix in 3 places, forget the 4th" is the pattern (this doc found exactly
  that gap).

### Complementary: a new cursor/iterator API for new and highest-value existing code

A pure cursor type (`text.chars()` yielding `(byte_offset, codepoint)`, or an
explicit `TextCursor` value) gives a **stronger guarantee** than the memo —
strict O(1) per step, no eviction/thrashing risk under interleaved access to
many strings at once — at the cost of being source-**incompatible**: every
call site that adopts it must be rewritten from indexed access to an
iterator loop. Recommend this as the **documented idiom going forward** for
new hot-loop code (tokenizers/parsers), and worth applying by hand to the
handful of highest-N existing sites such as the html tokenizer
(`html_tokenizer.spl`) and the CSS/HTML admission-gate loop found in §2 —
but not as a blanket migration of all 343 sites, since the side-table cache
already fixes those with no migration cost or risk.

Byte-index access (`byte_at`, already O(1), already in the codebase's own
migration playbook per the comments read in §1d/§2) needs no design change;
continue steering byte-framing code to it, as the existing comments already
instruct.

## 4. The mid-codepoint / invalid-UTF-8 trap — and a second defect it surfaces

Any cursor/cache design must decode exactly the way the existing fallback
walk already does: a lead byte that doesn't match a recognized UTF-8 pattern
is treated as **width 1, codepoint = the raw byte value** (see
`runtime_native.c:2338-2355`, the `else { width = 1; code = b0; }` implicit
default). The cursor must reuse this exact decoder, not a "cleaner"
UTF-8-only one that would panic or desync on invalid input — a mid-codepoint
slice is documented as a real, supported case, and the cache must not assume
codepoint-aligned or valid-UTF-8 input.

**Concrete finding specific to this codebase's `Value::StrBytes` variant**
(`compiler_rust/compiler/src/value.rs:1118`, the tree-walk interpreter's
representation for a mid-codepoint slice fragment holding raw, possibly
invalid bytes): `interpreter_method/mod.rs:900-933` handles a `StrBytes`
receiver for `char_code_at` (and every string method except `len`/`is_empty`/`bytes`)
by **lossily re-materializing it to a fresh `Value::text(String::from_utf8_lossy(bytes).into_owned())`
on every single call**:

```rust
Value::StrBytes(bytes) => {
    match method {
        "len" | "length" => ... "bytes" => ... _ => {}
    }
    let recv_val = Value::text(String::from_utf8_lossy(bytes).into_owned());
    include!("string.rs");
}
```

This conversion is itself an O(bytes.len()) scan **plus a fresh allocation**,
on every call, and it produces a **brand-new `Arc<String>` each time** — so
the `ASCII_MEMO`'s `Arc::ptr_eq`-keyed cache can never hit for a `StrBytes`
receiver; every call pays the conversion cost from scratch. A
`while i < s.len(): s.char_code_at(i)` loop over a `StrBytes` value is
**already O(N²) from this conversion alone**, independent of whatever fix
lands inside `char_code_at`'s own body. This is exactly the kind of trap the
brief warned about, and it means the fix must also touch the `StrBytes`
dispatch arm: implement `char_code_at` directly against the raw byte buffer
for a `StrBytes` receiver (same width-1-fallback decode as the other
engines), instead of routing through the lossy `String` round-trip. Recommend
folding this into the same change, since it's the same primitive under a
different receiver representation.

## 5. Estimate for the showcase cell — bounded where possible, flagged where not

**PROVED**: the showcase's actual HTML fixture,
`examples/06_io/ui/browser_common_elements_showcase.html` (loaded by
`web_render_file_gui.spl:303` via `read_file`), is **4848 bytes** and
**contains zero non-ASCII bytes** (`LC_ALL=C grep -c '[^ -~\t]'` → 0).

For this specific fixture, in engines 1a/1b/1c (post `4fb66c9678d`), the
whole-string-ASCII fast path applies on the very first call and every
subsequent `char_code_at` in a scan of it is O(1) — so the `_simple_web_html_source_admitted`
loop found in §2, and any other `char_code_at` scan over this exact
document, should already be **O(N) total, not O(N²)**, in three of the four
engines, on any binary built after 2026-07-28. **INFERRED**, not measured.

This is an important caveat to report back: **it is not obvious from static
reading that `char_code_at`'s residual quadratic cost is the live blocker
for this specific fixture**, given it's pure ASCII and the fast path landed
two days before current `HEAD`. Two things could still make it live: (a) the
binary actually exercised by the showcase predates `4fb66c9678d` (a stale
deployed artifact, a pattern this repo's own memory has hit before —
"Deployed compiler had NO LLVM codegen" 2026-07-29 is exactly this failure
shape), or (b) the actual execution path routes through 1d (the self-hosted
interpreter), whose `s[idx:idx+1]` shortcut is O(1) regardless of ASCII
content and so wouldn't be quadratic either, in which case `char_code_at` is
not the bottleneck for *this* fixture at all and the "one of two blockers"
framing needs re-checking against a fresh repro. Either way, N for this path
is bounded at ~4848 (the admission-gate scan) with additional smaller scans
inside the HTML tokenizer and CSS parser over the same order-of-magnitude
document — not large enough for O(N²) vs O(N) to be the dominant few-hundred-ms
cost unless the quadratic path is actually being taken.

**The one measurement this task's constraints allow me to name instead of
guess (per the "stop and say which measurement" instruction):** run the
showcase's exact failing command
(`SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 ... run examples/06_io/ui/web_render_file_gui.spl`,
per `doc/08_tracking/bug/web_showcase_repro_rerun_after_read_side_fix_2026-07-30.md`)
with `SIMPLE_WEB_PHASE_TRACE=1` (already-landed level-gated tracing, same
file, line 116-127) and a probe print bracketing
`_simple_web_html_source_admitted` specifically, against both a binary built
from current `HEAD` (post-fix) and the actually-deployed binary, to settle
which of (a)/(b) above is true before spending effort on this fix path for
cell #3 specifically. The cursor/cache design in §3 is worth doing
regardless (it's a real, still-partially-open defect touching 343 call
sites across the codebase), but whether it is *this* cell's blocker needs
that one run to confirm.

## Summary of PROVED vs INFERRED claims

| Claim | Status |
|---|---|
| 4 independent `char_code_at` implementations exist | PROVED (read all four) |
| 3 of 4 got an ASCII-fast-path fix on 2026-07-28 (`4fb66c9678d`), landed on current `HEAD` | PROVED (git log -S, ancestor check) |
| Those 3 still fall back to a full O(index) walk once a non-ASCII byte precedes the query index | PROVED (read the fallback branch) |
| Self-hosted interpreter (1d) uses byte-offset slicing, is O(1) but incorrect on non-ASCII | PROVED the O(1) shape (`rt_slice` reads `data+begin` directly); the incorrectness is a straightforward semantic reading of "byte offset used as char index", not executed |
| 481 raw occurrences / 343 `.spl` call sites | PROVED (grep, deduped) |
| 278 loop-shaped call sites | INFERRED (heuristic window grep, not per-site verified) |
| `_simple_web_html_source_admitted` is a live, unconverted O(N)-or-O(N²) scan in the showcase's own path | PROVED it's unconverted char_code_at-in-a-loop; whether it's currently O(N) or O(N²) for the real fixture is INFERRED |
| Showcase HTML fixture is 4848 bytes, pure ASCII | PROVED |
| `Value::StrBytes` receivers re-pay an O(N) lossy conversion on every method call, defeating any Arc-identity cache | PROVED (read the dispatch arm) |
| Whether `char_code_at` is *currently* the live blocker for showcase cell #3 given the fixture is pure ASCII | UNRESOLVED — named the exact measurement needed, not guessed |
