# Uncapped full CLI parse-failure classification

## Recorded failure

The diagnostic Windows run at
`D:/dev/uncapped-logic-build-20261002/full-cli-llvm/result.json` completed all
2,493 parse/surface inputs, then exited 1 with 130 failed source paths. Peak
process-tree RSS was 8,281,864 KiB and no memory cap was enforced. The receipt
reports a quiescent process tree; this is not an RSS-cap failure.

- Source: `08e1e3cfc72655614fe5a30d7ace67700faf6f6c`
- Source tree: `d2cb9b4b6c0885dedef9e4eaedd434c3eb0f882d`
- Producer SHA-256: `70da44fb1d731afc2dcd27ef095751874c5ea0334937510fec51d11654cce9bb`
- Current release comparison: `1538f7da26`

## What the log proves and omits

The log identifies failed paths but contains no actual `[parser_error]`
location/reason records. Each aggregate message refers to nonexistent preceding
diagnostics. Consequently it proves the driver's parse-failure state, not 130
distinct grammar bugs. Syntax, stale parser state, cache restoration, and
diagnostic lifetime must remain distinct hypotheses until a bounded probe
returns concrete receipts.

None of the 130 failed source files changed between the frozen source commit
and the compared release. The frontend delta is only the already-landed module
binding annotation continuation fix (`34089f9089`). None of these 130 files has
that fix's module-level `val/var name:` newline trigger. No failed path can be
marked fixed on release from this comparison alone.

One failed source, `src/compiler/15.blocks/blocks/modes.spl`, contains comments
and only `export use compiler.frontend.block_types.*`. This is the smallest
probe target and makes a blanket grammar attribution particularly weak.

## Bounded diagnostic probe

`test/fixtures/uncapped_parser_diagnostics/main.spl` tests that pure-export
source shape, a valid function, and malformed input. It repeats valid inputs
after the malformed control to detect stale error state. The probe uses the
existing scalar checked-parse return and first-error text receipt; it does not
change parser grammar or invent a replacement error flag.

The root admitted bounded probes with 300-second compile timeouts and a
60-second run only if compilation succeeds.
Evidence, dedicated cache/output, fixture/producer hashes, and admission are in
`D:/dev/uncapped-parser-probe-20261002`. A separate source worktree retains the
exact 08e source revision. The original full CLI frozen source and evidence are
unchanged. Do not repeat the large CLI build to rediscover these paths.

## Probe outcomes (three-cycle limit reached)

| Probe | Outcome | Peak RSS KiB |
| --- | --- | ---: |
| Parser implementation harness, 1 GiB sampled limit | Exit 88 at HIR 33/90; fixture not executed | 1,049,528 |
| Same harness/cache, admitted 2 GiB sampled limit | Exit 88 during MIR; fixture not executed | 2,098,276 |
| Direct scalar entry importing exact `modes.spl`, 2 GiB limit | Four-module parse/HIR/MIR and three code-bearing objects completed; link failed because isolated sparse source lacks runtime.c | 190,288 |

Both capped runs report `rss_cap_enforced=1`, `hard_memory_limit=0`, and
`quiescent=1`: these were sampled RSS termination limits, not hard OS allocation
limits. The final probe also reports a quiescent tree. Its missing runtime source
is an isolated harness configuration limitation; it is not a parser failure.
No fourth build was launched.

The direct probe rejects an intrinsic grammar-defect explanation for
`modes.spl` on this exact producer/source. It does not explain all 130 failures
or prove that parser state, cache restoration, or lifetime handling is correct
in the large closure.

## Confirmed diagnostic loss and source fix

All ordinary driver parse-error branches discarded the parser's available error
text and stored only a pointer to stdout. The transient failure helper also
constructed that placeholder after parser-scope teardown. These branches cannot
retain a diagnostic that was suppressed or lost at that output boundary.

The candidate now snapshots the existing first-error receipt, falling back to
the retained error list, into each aggregate error. Borrowed-scope paths allocate
the message after pausing scratch allocation and before ending the scope. When
neither receipt exists, they explicitly report missing diagnostic evidence.
Parser initialization clears first-error text per module so a preceding failed
file cannot be misattributed to the next file. Error verdicts and grammar are
unchanged. Existing parser-owned environment receipt helpers are reused; there
is no new raw host-access boundary.

`parse_diagnostic_receipt_spec.spl` covers suppressed output, mixed
bad/good/different-bad modules, retained text, missing receipts, rejected cold
error cache publication, and the real flat-pool warm restore boundary after an
error. It does not claim disk/CAS cache transport verification.
These regressions and native lifetime verification remain UNRUN after the three
admitted diagnostic builds. No grammar fix or all-130 known-fixed claim is made.

Bounded source review found no production P0/P1 lifetime/stale-message defect.
It corrected a test authoring error: `parse_module_silent_checked` returns a
failure flag, not success. The candidate fixture/spec uses that convention;
neither earlier parser-implementation fixture executed, so no execution receipt
is reinterpreted by this correction. Frozen diagnostic inputs remain unchanged.

Integration dependency: preserve `06572a9d8` / PR #2208's complete frontend
owner/Result promotions when combining overlapping driver changes. This patch
only adds diagnostic text capture at the already-paused ownership boundary;
it does not add a second arena root or replace those owner promotions.
