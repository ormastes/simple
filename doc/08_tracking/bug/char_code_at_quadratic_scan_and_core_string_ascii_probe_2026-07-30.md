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
