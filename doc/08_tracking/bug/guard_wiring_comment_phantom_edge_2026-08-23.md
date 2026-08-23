# `check-guard-wiring.shs` counts a basename in a COMMENT as a wiring edge

- **Status:** OPEN — mechanism located and independently reproduced twice; no fix landed
- **Date:** 2026-08-23
- **Area:** `scripts/check/check-guard-wiring.shs` (~lines 114-136), the
  `push-guard-wiring` blocking gate
- **Severity:** High — this is the gate the whole repo queues behind, and it
  certifies the one property it cannot actually observe
- **Handoff (mechanism, not re-derived here):** `/mnt/data/tmp/handoff/guard_wiring_comment_phantom_edge.md`
- **Related:** `check_guard_wiring_48_unwired_triage_2026-08-08.md`,
  `guard_wiring_optout_false_exemptions_2026-08-06.md`,
  `core_c_capsule_gate_wrongly_opted_out_of_guard_wiring_2026-08-06.md`

## Summary

The wiring graph is built by grepping guard **basenames out of file CONTENT**.
Any occurrence counts — including inside a `#` comment. So a guard that merely
*mentions* another guard by basename is recorded as **invoking** it, and once the
mentioning file is itself reachable from a root, every guard it names inherits
"wired" status.

This matters more than a cosmetic miscount: `push-guard-wiring` is a BLOCKING
gate, three push outages on 2026-08-23 traced to guard wiring, and lanes hitting
it reached for `--no-verify`, which skips every other gate too. If the gate
certifying wiring can be satisfied by prose, its PASS is weaker than everyone has
been treating it.

## Two independent reproductions, different methods

**(A) Sibling lane** (`/mnt/fast/wt/use-resolve-1`, origin/main `095a0236045`).
Adding one new guard whose *header comment* cited three sibling guards by full
basename flipped those three from correctly-baselined-unwired to
`stale_baseline_now_wired` — the ratchet then demanded their baseline rows be
REMOVED. Nothing about those three guards changed. The delta is exactly the four
characters `.shs` inside a `#` comment:

```
pristine (script absent):                      ... 0 stale/bad baseline
with header citing siblings as `<name>.shs`:   ... 3 stale/bad baseline
                                               stale_baseline_now_wired=check-dangling-imports.shs
                                               stale_baseline_now_wired=check-no-phantom-deep-stdlib-imports.shs
                                               stale_baseline_now_wired=check-no-phantom-module-imports.shs
same script, citations written without `.shs`: ... 0 stale/bad baseline
```

**(B) This lane** (`/mnt/fast/wt/rt-build-1`), while wiring the two guards landed
by `bf8044998ce`. Run as a two-step neuter, because the first step alone does not
isolate comments:

```
1. both `run:` lines deleted (they were the only mentions of either basename)
   -> FAIL — 881 guard(s) checked, 2 NEW unwired
2. both `run:` lines deleted AND a comment naming both basenames appended
   -> PASS — 881 guard(s) checked, 141 invoked, 0 NEW unwired
```

Step 1 establishes that a genuine wiring PASS is earned by the invocations.
Step 2 establishes that a comment alone reproduces that PASS with no invocation
anywhere in the file.

## Mechanism

```sh
$GREP -r -I -l -F -f "$_wd/guards" $(cat "$_wd/searchdirs")   # ~line 118
... | $GREP -o -F -f "$_wd/guards"                            # ~line 136
```

The only prose filter applied first (~lines 134-135) is the
`*_note=` / `*_report=` / `*_report_note=` assignment shape. **That filter is
itself evidence the false-edge problem was already known in another shape** — its
in-tree comment says, verbatim, that without it such a line "creates a phantom
wiring edge". A plain `#` comment is simply a second shape of the same bug that
was never filtered.

## Consequences

1. **"141 invoked" is an upper bound, not a count of genuinely-wired guards.**
   Some unknown fraction of that number may be comment-only. Anyone reasoning
   about wiring coverage from that figure is over-trusting it. The same applies
   to every historical invoked-count in the records listed above.
2. **It silently un-baselines other lanes' tracked debt.** Phantom edges make the
   ratchet report their baseline rows as stale and instruct their removal, after
   which those guards are no longer tracked as unwired at all.
3. **It is self-amplifying.** The more thoroughly a new guard documents its
   relationship to existing guards — exactly what reviewers ask for — the more
   phantom edges it creates. The current workaround in
   `check-use-target-resolves.shs` is to cite siblings *without* the `.shs`
   extension, i.e. to write worse documentation to appease the checker.

## Fix direction

Recognise **real wiring edges** rather than any textual occurrence:

- a workflow `run:` step that invokes the script,
- a hook invocation (`sh <path>`, `. <path>`, `"$ROOT"/<path>`, `run_child ... <name>`),
- a `config/check/must_check_gates.sdn` ledger row.

Stripping leading-`#` comment lines before the basename grep is the minimum and
matches how the `*_note=` shape is already handled; call-position matching is the
narrower and more faithful variant, since call position is what the BFS already
*means* by "invokes".

## The honest bar for any fix

**A stricter scan must not regress into false NEGATIVES.** A guard genuinely
wired through an unusual path would then read as unwired and block pushes — which
is the exact failure mode this repo spent 2026-08-23 fighting, merely inverted. A
fix therefore needs, before landing:

- a fixture proving a comment-only mention reads as UNWIRED, and
- fixtures proving each real wiring shape still reads as WIRED (workflow `run:`,
  hook invocation, ledger row, and the indirect `run_child`/sourced-script forms),
- a full-tree before/after diff of the invoked set, with every guard that changes
  status explained rather than accepted.

Until then the workaround stands and should not be "helpfully" undone:
`check-use-target-resolves.shs` cites its siblings without the `.shs` extension
and carries a header note saying why.
