# Lint's lexical scanners walked every character one interpreted step at a time

- **Filed:** 2026-08-23
- **Status:** FIXED
- **Area:** `src/compiler/35.semantics/lint/` (interpreted lint hot path)
- **Landed:** see §27 row
- **Class:** avoidable per-character interpreted work (same family as `c6f190752ff`)

## Symptom

The SIGPROF interpreter sampler (`SIMPLE_INTERP_SAMPLE=1`, landed `8c6bfaca127`)
put the two largest self-time frames of an interpreted `simple lint` run inside
two text scanners, not inside the compiler:

| frame | self time |
|---|---|
| `count_triple_quotes` | 5.8% |
| `raw_rt_lexical_code_lines` | 5.5% |

An earlier lane looked at these, concluded they were "per-char interpreted
loops, proportional to work — not interpreter bugs", and stopped. That
conclusion was wrong in its premise: the work was **not** proportional to
anything the lint has to know. Both loops paid full per-character interpreted
cost on characters that no branch of the scanner can act on.

## Mechanism

`raw_rt_lexical_code_lines` blanks comments and string literals while
preserving columns. Per character of every line it did:

- `raw_line.substring(i, i + 1)` — one interpreted allocation for the 1-char slice;
- `raw_line.substring(i, i + 3)` — a second allocation, taken **unconditionally**
  to test for `"""`, even though a `"""` can only start at a `"`;
- `raw_line.len()` re-evaluated in the loop condition;
- `pieces.push(ch)` — one array mutation per character, later `join`ed.

So a 60-character line with no quote and no `#` — the shape of most code lines —
cost ~120 interpreted string allocations and 60 array pushes to reproduce
itself byte-for-byte.

`count_triple_quotes` had the same shape: a 3-character `slice` per character
of every line, on lines that contain no `"""` at all.

## Fix

Run-based scanning. No algorithm or semantics change; the state machine and its
branches are untouched.

- `count_triple_quotes`: `if line.index_of("\"\"\"") < 0: return 0`. The walk can
  only ever count occurrences of that substring, so a line without it is 0 by
  construction. `index_of` is a native scan.
- `raw_rt_lexical_code_lines`:
  - whole-line fast path — outside a string/triple, a line with no `"` and no
    `#` is copied verbatim by the walk, so return `raw_line` and skip. **Landed
    independently by a concurrent lane while this work was in flight; kept as
    upstream wrote it, and the numbers below separate its share from this
    commit's.**
  - ordinary text inside a line — copy the whole run up to the next `"` or `#`
    with one `substring`, instead of one push per character;
  - comment tail and triple-quoted spans — blank with one `" ".repeat(n)`
    instead of one `push(" ")` per character;
  - the 3-char `"""` probe is taken only when the current character is `"`;
  - `raw_line.len()` hoisted out of the loop.

Architecture, value semantics, COW behaviour, SFFI contracts and MDSOC layering
are unchanged: these are two pure functions in one layer, edited in place.

## Evidence

Controlled A/B — one tree, one binary
(`/mnt/data/worktrees/goal-main-1/bin/simple`, interpreted), the fix reverted
and restored with `git stash`, nothing else changed.

**Correctness (checked first, and the bar for shipping):**

- 150 real `src/**/*.spl` files, frozen corpus, full output of BOTH functions
  dumped and `diff`ed: **byte-identical**, 57,385 emitted lines.
- Adversarial fixture set (`#` inside a string, a quote inside a comment, an
  escaped quote, `""""`, an unterminated string carrying state across a line
  boundary, multi-line triple-quoted blocks): byte-identical, asserted in the
  spec against an inlined copy of the original per-character walk.
- End-to-end `simple lint src/lib/common/text.spl`: output identical.

**Performance, on the same 150-file corpus:**

Measured against two baselines, because a concurrent lane landed the whole-line
fast path (`clean_line` returns `raw_line` when the line holds neither `"` nor
`#`) while this work was in flight. Both are reported; the second is the one
this commit is responsible for.

| baseline | measure | pre | post | ratio |
|---|---|---|---|---|
| `01507771ec8` (neither fix) | `ARR_MUT_CALLS` | 1,267,276 | 218,684 | **5.8x** |
| `01507771ec8` | wall | 30.88s | 8.19s | 3.8x |
| current upstream (whole-line fast path already landed) | `ARR_MUT_CALLS` | 740,481 | 218,684 | **3.4x** |
| current upstream | wall | 28.89s | 12.04s | 2.4x |

The whole-line skip alone therefore accounted for ~40% of the pushes; the
in-line run scanning in this commit accounts for the remaining 3.4x. The two
compose — the whole-line skip cannot help a line that contains a single quote
or a trailing comment, which is most non-trivial code.

`ARR_MUT_CALLS` is the deterministic pin: it counts identifier-receiver array
mutations, which is exactly the `pieces.push(...)`-per-character mechanism.
Wall time on this shared box moves 2x between runs of identical code and is
reported only as corroboration.

## Regression pins

- Spec: `test/05_perf/lint/lint_lexical_char_walk_perf_spec.spl` — 4 cases.
  Two assert byte-identity against an inlined copy of the pre-fix per-character
  walk; they pass in BOTH directions, by design, because they guard semantics,
  not speed. Two are ratio pins measured inside a single run, because absolute
  seconds on this shared box move 2x between runs of identical code.
  Verified against the CURRENT upstream base (whole-line skip already present),
  fix stashed and restored, nothing else changed:

  | pin | pre | post |
  |---|---|---|
  | long run vs 1-char runs, same line length, both quoted | 728,639us / 824,636us — ratio **1.13**, RED | 59,947us / 928,322us — ratio **15.5**, GREEN |
  | docstring scan, lines with no `"""` vs lines full of them | 159,900us / 201,488us — ratio **1.26**, RED | 12,140us / 126,973us — ratio **10.5**, GREEN |

  The first pin deliberately puts a quote on BOTH sides so the earlier
  whole-line skip cannot satisfy it, and asserts the two inputs are the same
  length before reading the ratio — a guard-the-guard, since a ratio between
  differently-sized inputs would be meaningless.

- Guard rows in `scripts/check/check-perf-regression-tests.shs` pin each of the
  five mechanisms by source text, so a stale-snapshot clobber is caught the hour
  it lands.

## Not done here

`char_slice` / `char_code` / `char_code_inline` / `advance` in the lexer
(`src/compiler/10.frontend/core/`) are the next targets in the same family and
are untouched by this change.
