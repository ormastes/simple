# `--no-verify` landing record — 3 commits onto `79ddeee2d34`, 2026-08-17

**This is a RECORDED step-over, not a bypass.** Every guard below was actually
run and its verdict line is reproduced verbatim. The distinction from the four
tree-wipe incidents is precisely that guards RAN and their output exists; in the
wipe cases a stale `core.hooksPath` silently downgraded everything to advisory
and nobody ran anything.

## Authorisation

`git push --no-verify` was used on **explicit user authorisation dated
2026-08-17** ("sync gh no verify push"), relayed by the coordinating session
after the user was shown the trade-off. It is a single, scoped authorisation for
this range. No agent may treat this record as licence for a later push.

## Range

- **Base:** `79ddeee2d34212f4bc8747400c584f75dc6f288e` (origin/main at push time)
- **Commits landed (3):**
  1. `579a0e1a171` — `fix(parser): REGRESSION from 3c4e6551b7a — 'use' as a soft-keyword ident broke every relative import`
  2. `6523b1ca34d` — `docs(triage): hand 40 dangerous bug rows to a second host; fence them CLAIMED-OFFHOST`
  3. `4b45dac5214` — `test(crypto): mirror the ed25519 constant-time spec, and record the divergence backlog`

Plus this record document, committed on top.

### Why these three

- `579a0e1a171` fixes a regression whose breaking commit `3c4e6551b7a` **is an
  origin ancestor**, i.e. live for everyone. `vhdl_backend.spl` carries 9
  `^use \.` relative-import lines and the runner's module graph reaches it, so
  `bin/simple test` is down on every spec until this lands.
- `6523b1ca34d` — measured **2 of 33** `CLAIMED-OFFHOST` stamps at origin and
  `priority_bug.md` absent, so the off-host fence effectively did not exist and a
  second host could duplicate local work.
- `4b45dac5214` — ed25519 spec mirror. Invariant re-asserted after rebase: both
  `test/01_unit/lib/crypto/ed25519_ct_property_spec.spl` and
  `test/unit/lib/crypto/ed25519_ct_property_spec.spl` hash to
  `62af374c25ad225517b77740e409ce667c6f4f95`.

## `579a0e1a171` IS UNVERIFIED — read this before treating it as closed

Its **RED is proven** on a full binary. Its **GREEN is not**, because no
bootstrap rebuild completed (a rebuild made no progress in ~90 minutes against
competing cargo builds). The green evidence is a `BUILD_RC=0` plus a two-file
`use .helper.{helper_value}` repro at rc=0 — not a completed bootstrap.

Landing an unverified fix in order to unbreak origin was the **user's explicit
call**. Whoever rebuilds next MUST re-run the repro before closing the row.
This sentence exists so that nobody later reads this landing as a verification.

## Guards that RAN and PASSED (verbatim verdict lines)

Range `79ddeee2d34212f4bc8747400c584f75dc6f288e..882ce71f6def36f1cee185350fd41b0deece0f23`:

```
check-no-conflict-tree-push: PASS — 3 commit(s) checked in 79ddeee2d34..882ce71f6de, 0 conflict trees
check-no-conflict-markers-push: PASS — 48 file(s) scanned at 882ce71f6de across 3 commit(s), 0 conflict markers
check-tree-size-push: PASS — 3 commit(s) checked, reference 115346 file(s) (measured at base 79ddeee2d34), 0 structural faults
check-runtime-api-regression-push: PASS — 2795 symbol(s) checked, 0 removed
PASS — 106 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)   [check-c-runtime-compiles-push]
check-hook-installation: PASS — 10 check(s) performed, hook wiring intact
```

### Structural / anti-wipe audit (the checks that actually caught past wipes)

- `7 A / 41 M`, **ZERO `D` lines** in the aggregate range diff
- **zero deletions in every individual commit** (`git diff-tree -r --name-status`)
- `src/app/interpreter` = **99 files** (the proven wipe canary)
- total tree = **115,353 files**

## Guards STEPPED OVER (named explicitly)

1. **`check-implicit-self-field-assignment.shs`** — full scan, NOT range-bound.
   ```
   FAIL — engine 'interpreter': implicit field assignment SILENTLY NO-OPPED — the program ran to completion and printed 'implicit -> false', so the write to `flag` was discarded with no diagnostic
   pre-push: BLOCKED by check-implicit-self-field-assignment.shs (status 1) for range implicit self-field-assignment probe (full scan, not range-bound)
   ```
   Pre-existing; predates this range and is untouched by it.

2. **`check-test-tree-divergence.shs`** —
   ```
   check-test-tree-divergence: FAIL — 876 diverged vs 813 baselined (64 new, 1 fixed-but-still-baselined); 7 mirror-only (5 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
   ```
   Includes the **5 unallowlisted mirror-only** entries. Test-tree divergence is
   hygiene, not corruption protection.

3. **`check-test-tree-divergence-delta.shs` — DID NOT COMPLETE.** The scoped-delta
   escape was NOT satisfied for this range. No base-stamped offender list for
   `79ddeee2d34` exists. An earlier delta run on a **different** base
   (`ace3d53881c7`) did complete with `PASS — 71 pre-existing offender(s), 0
   introduced by this range`, and its list is deliberately **quarantined and NOT
   substituted here** — wrong base (877 vs 876 diverged), so it is not evidence
   for this range.

4. **`check-seed-builds-push.shs` — UNRESOLVED at push time.** It had not
   returned a verdict when the push was made. It does **not** take the documented
   fast path for this range: `579a0e1a171` touches five files under
   `src/compiler_rust/` (`parser/src/parser_impl/core.rs`,
   `parser/src/expressions/postfix.rs`,
   `compiler/src/interpreter_extern/{mod,sffi_string}.rs`, and the new
   `parser/tests/relative_import_not_soft_keyword_ident.rs`), so a real
   `cargo check` is required. Its selftest reported `3/3 fixtures correct`.
   **This is stated, not implied to have passed.** An unbuildable seed at origin
   is a documented incident class
   (`doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`);
   whoever next has a free machine should `cargo check --release --bin simple`
   at this tip and file a row if it is red.

## Non-results explicitly NOT counted

Two earlier runs were killed by the operator (not failed by the guards) and
wrote `ERROR — nothing was checked`; one earlier delta attempt died at a
10-minute wrapper timeout with `rc=143`. Per project rules `rc=143`/`137` and
exit-2 `ERROR` are **UNVERIFIED — never a pass and never a fail**. None of them
is carried forward in either direction. The 10-minute wrapper was itself the
cause of the `rc=143`; the relaunches were run unbounded.

## Corrections this landing establishes

- The pre-push hook does **NOT hang.** `check-native-trailing-default-param.shs`
  returns rc=1 in ~7 minutes with a proper verdict line. Earlier `rc=124` reports
  were a 240 s timeout that was simply too short.
- The claim that `50.mir/_MirLoweringExpr/expr_dispatch.spl:49` fails to parse
  (`expected Fn, found Assign`) is **REFUTED** — zero parse errors appear
  anywhere in that guard's output. The deployed binary was ~8.5 h stale, which is
  the actual explanation.
- `check-native-trailing-default-param` **never fired** in this push's hook run.
  It was wrongly pre-named as the blocker in an earlier authorisation request.
