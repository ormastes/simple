# check-no-direct-rt: a bare run is not the gate, and the SPipe migration cycle used the bare form

Date: 2026-09-05
Status: scoping defect FIXED in `scripts/spipe/rt_migration_cycle.shs`; measurement
caveat quantified and left open; no baseline moved.

## Claim under test

"`sh scripts/check/check-no-direct-rt.shs` is FAIL and it is a named gate."

## Finding: the named gate is GREEN; the bare run is a different population

The named gate is not the bare command. Both rows in
`config/check/must_check_gates.sdn` spell it with `--roots src`:

- `:6`  `push-no-direct-rt, push, true, tree, "sh scripts/check/check-no-direct-rt.shs --roots src"`
- `:40` `no-direct-rt, bootstrap, false, automated, "sh scripts/check/check-no-direct-rt.shs --roots src"`

and `check-push-must-pass.shs:325,359` dispatches `--roots src` for both.
Measured 2026-09-05:

    PASS — 16244 file(s) scanned (roots=src, src=6230), forbidden=6230, extern_decls=6459 (baseline 7776)

The gate is green with 1546 sites of headroom. `src` debt has never exceeded
the baseline; it is the widened *default* `--roots` (changed 2026-08-28 to
`src,examples,tools,scripts,test`) that produces the FAIL, by comparing a
five-root population against a baseline recorded under one root. The script's
own header already forbids that comparison: "a baseline recorded under one
--roots set is not comparable to a run under a different --roots set".

So this is conclusion (a) — a scoping mismatch — but the mismatch is *inside
callers of the script*, not inside the gate. Nothing needed re-scoping in the
gate and nothing needed re-baselining.

## Why the default was NOT narrowed to `src`

The obvious "fix" — `ROOTS="src"` — is wrong and was rejected.
`scripts/check/check-simpleos-mission-critical-release.shs:348` runs this
script **bare** with `--critical`, and its comment plus
`doc/07_guide/app/spipe/mission_critical_robust_sw.md` § No-direct-rt lane
record that as deliberate: a mission-critical release "must cover its own
examples/tools/scripts/tests too", with zero baseline grace. Narrowing the
default would silently shrink that lane's scope. That is weakening a gate, and
the lane is documented as honestly RED, not as passing.

## The one real defect found and fixed

`scripts/spipe/rt_migration_cycle.shs` (whose stated goal is "drive the
check-no-direct-rt baseline to zero") invoked the gate **bare** at its two
verification steps and then `git add`ed the src-scoped
`scripts/check/no_direct_rt_baseline.txt`. Since the 2026-08-28 widening this
compared 27454 against 7776, so both steps always failed and the cycle was
structurally unable to commit any migration. Both call sites now pass
`--roots src`, matching the baseline they verify against, with the reasoning
inline. `sh -n` clean; the gate's `--selftest-only` (16 fixtures, fatal) still
passes.

## Tracked residuals (measured 2026-09-05, nothing gated by a baseline)

| invocation | verdict |
|---|---|
| `--roots src` (the named gate) | PASS, forbidden=6230, baseline 7776 |
| bare, ratchet mode (no wired lane uses this) | FAIL 27454 vs 7776 — scope/mode mismatch |
| bare `--critical` (release lane) | FAIL 27454, zero-tolerance, no baseline |

Wide-roots breakdown: src 6230, examples 1344, tools 14, scripts 308,
test 19558; extern_decls 13207. `mission_critical_robust_sw.md:45` records
27,685 on 2026-08-28 — a 231-site improvement, not a re-baseline.

## Open: RT_RE counts pure-Simple functions that follow an `rt_` naming convention

`RT_RE='^[^#]*\brt_[a-z0-9_]*\('` cannot distinguish a runtime extern call
from a Simple function whose name starts with `rt_`. The allowlist already
documents this for `src/lib/nogc_sync_mut/rt_hal/` (~160 sites) and names the
permanent fix as a scanner prefix rule. Quantified here for the largest single
instance: `src/compiler/35.semantics/rt_criticality_validation.spl` contributes
155 forbidden sites and **none** is a runtime call —
`rt_expr_dispatches` (50), `rt_expr_allocates` (47), `rt_block_dispatches`
(17), `rt_block_allocates` (17), plus `rt_stable_fn_id`, `rt_module_matches`,
`rt_name_effects`, `rt_module_ids`, ... all compiler predicates defined in
Simple and imported from `compiler.frontend.rt_criticality_registry` /
`compiler.semantics.rt_hal_tag`. Not fixed in this pass: a scanner exclusion
changes `--critical` semantics for the release lane and needs its own selftest
fixture.

## Blocked: no TDD lane on this host for `src` call-site conversion

The task's conversion work (raw `rt_*` -> typed `std.*` alias) requires the
covering spec to PASS before the change. Three binaries and two invocation
forms were probed; none gives a green baseline:

- `bin/simple test ...` -> `error: unknown command 'test'`. `bin/simple` is a
  zsh wrapper onto `bin/release/aarch64-apple-darwin-macho/simple`, which is
  the bootstrap CLI (only `compile`/`native-build`).
- `bin/release/aarch64-apple-darwin-macho/simple_seed test ...` ->
  `compile failed: parse: in ".../src/app/io/mod.spl": Unexpected token:
  expected expression, found Colon`.
- ...`simple_seed run test/01_unit/app/itf/adapter_minio_spec.spl` ->
  `semantic: variable \`always_inline\` not found`.
- `bin/release/aarch64-apple-darwin/simple` (`Simple v1.0.0-beta`, the stage4
  full CLI) DOES run the suite, but fails on current language constructs:
  `adapter_minio_spec.spl` -> `1 total, 0 passed, 1 failed` with
  `semantic: variable \`always_inline\` not found`;
  `crc32_text_crosslang_spec.spl` -> `6 total, 5 passed, 1 failed` with
  `semantic: function \`unsafe\` not found`.

That is the stale-deployed-binary defect recorded in
`.claude/rules/language.md` and
`doc/08_tracking/bug/stale_deployed_binaries_reject_current_language_sspec_scorer_unrunnable_2026-09-05.md`.
A pre-existing red spec cannot serve as a TDD baseline: there is no way to
distinguish "still passes" from "was already failing".

No call site was converted, deliberately: an unverified conversion that makes a
gate greener while breaking behaviour is worse than the debt. The prepared
target list, for a lane with a working runner, is the "alias never exported"
pattern — e.g. `src/lib/nogc_sync_mut/io/http_sffi.spl` (allowlisted provider)
declares `rt_http_request`/`rt_http_download` as externs and exports **no**
typed wrapper, so `src/app/itf/adapter_minio.spl:10` and
`src/app/devhub/cmd_api.spl:6` import the raw names (6 forbidden sites).
Adding typed wrappers inside the provider and switching the two importers is
free of ratchet cost and is the sanctioned direction.

Residual left behind: **6230** forbidden sites in `src` (gate green, baseline
7776 untouched); **27454** across all five roots for the `--critical` release
lane.
