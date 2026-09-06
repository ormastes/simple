# A spec file's pass/fail verdict is forgeable from an example's NAME

**Status:** OPEN — root cause understood and localised to a defect CLASS; two
`.spl` parsers hardened here, but the LIVE producer on the seed path is NOT yet
located, so the symptom still reproduces. Read "What is NOT fixed" before
believing any part of this is closed.
**Found:** 2026-08-17, lane-1 partial-fix sweep, while writing the detection
spec for `feature_block_not_a_bdd_keyword_2026-08-04.md`.
**Severity:** HIGH — this is a test-verdict integrity defect. The repo has been
burned repeatedly by verdicts that did not mean what they said (see
`.claude/rules/vcs.md` on guards that "fail open", and the standing rule that
only an explicit `Results:` line settles an outcome). This defect attacks that
last line of defence directly.

## Symptom (minimal, reproduces on BOTH seeds)

```spl
use std.spipe.*
describe "d":
    it "registers each example separately, not as one synthetic failure":
        expect 1 to_equal 1
```

```
$ bin/simple test <that file> --no-session-daemon --sequential \
      --no-cache --no-cover-check --timeout 120

  ✓ registers each example separately, not as one synthetic failure
1 example, 0 failures
SPEC FILE VERDICT: ... declared>=1 executed=1 passed=1 failed=0 dropped=0
error: test-runner: spec failed
Results: 33 total, 1 passed, 32 failed
```

The child ran ONE example and PASSED it, and says so twice (`1 example, 0
failures`, `executed=1 passed=1 failed=0`). The file-level summary reports
**33 total, 32 failed** and a hard `spec failed`. 32 failures were invented out
of an example's name.

Verified on two independently built binaries:

| binary | result |
|---|---|
| deployed `bin/simple` (Rust seed, 2026-08-16) | `Results: 33 total, 1 passed, 32 failed` |
| freshly built seed (2026-08-17, this lane's tree) | `Results: 33 total, 1 passed, 32 failed` |

So it is **pre-existing**, not introduced by this lane's changes.

## Root cause (the class)

The file-level verdict is not taken from the child's structured result. It is
**text-scavenged out of the child's stdout**, with a predicate that any line
can satisfy:

`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:244`
```spl
elif clean.contains("example") and clean.contains("failure"):
    val examples_count = extract_number_before(s: clean, keyword: "example")
    val failures_count = extract_number_before(s: clean, keyword: "failure")
```

and the same shape again at
`src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:145`
(`bdd_summary_counts`), where every parse failure was additionally swallowed by
`.to_int() ?? 0`.

Two independent weaknesses compose:

1. **The predicate is a bare substring test over EVERY output line.** An
   example's own printed name is an output line. Any `it` whose name contains
   both the words "example" and "failure" is parsed as if it were a summary
   line. The name is attacker-controlled in the ordinary sense that any spec
   author writes it, and it is not an exotic string — the one above was written
   by accident, as a plain English description of what the example checks.
2. **`extract_number_before` scavenges digits from wherever it lands.** The
   line it was fed still carries ANSI colour escapes, and `\x1b[32m` — the
   green code — contains the digits **32**. That is precisely the phantom
   failure count. (Stated as the strongly-indicated explanation, not as a
   proven one: `32` matching the green ANSI code exactly, on a line with no
   other digits, is not a coincidence worth arguing with, but the arithmetic
   was not stepped through in a debugger.)

### Why this is worse than a false RED

The instance found was a false RED, which is loud. The same mechanism runs in
the other direction: a line contributing `total` without contributing
`failures` **adds passes**. A name of the form `"... 99 examples, 0 failures
..."` is an ordinary-looking English sentence that inflates the pass count of
the file containing it. Nothing in the pipeline distinguishes a summary the
runner printed from a sentence an author wrote.

## What was changed here (hardening, NOT a proven fix)

Both `.spl` parsers now require a line to have the SHAPE of a summary before
they will believe it: `<int> example|examples, <int> failure|failures`, with a
trailing `(123ms)` allowed. A non-numeric first token, a missing keyword, or a
head with anything other than exactly `<count> <word>` is rejected outright
instead of being coerced to `0`.

- `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_single.spl`

Confirmed no regression: normal specs still count correctly after the change
(`2 total, 2 passed, 0 failed` for a clean 2-example file; `2 total, 1 passed,
1 failed` for a genuinely failing one).

## What is NOT fixed, and what is NOT known

- **The symptom still reproduces.** After both edits, the probe still reports
  `Results: 33 total, 1 passed, 32 failed`. Since `src/lib/**` is read as
  SOURCE on every run (no build needed — see `.claude/rules/commands.md`), the
  edits ARE live; they simply are not on the path that produces this line under
  `bin/simple test`. **The live producer has not been located.** It is most
  likely a third implementation inside the Rust seed rather than either `.spl`
  parser. Whoever picks this up should start by finding what actually emits the
  `Results: N total, ...` line on the seed path, and check it for the same
  substring-predicate shape.
- The two hardened parsers were verified only for absence of regression on
  ordinary specs. Their fix was never observed to CHANGE the forged verdict,
  because they are not the live path here. They are hardening of the same
  defect class in the pure-Simple lane (the default tooling per `CLAUDE.md`),
  filed honestly as such.
- The false-GREEN direction was reasoned about, not demonstrated. No spec was
  constructed that forges a passing verdict.
- Only the seed lane was exercised. The self-hosted pure-Simple lane was not.

## Detection

`test/01_unit/compiler/bdd_feature_group_keyword_spec.spl` carries a comment
recording why its second example is NOT named with the triggering phrase. That
is a signpost, not a test. **No spec pins this defect yet** — writing one
requires first locating the live producer, since a spec asserting the correct
count would simply be another RED against an unfixed bug rather than a guard.
Left deliberately unpinned rather than pinned against the wrong parser.
