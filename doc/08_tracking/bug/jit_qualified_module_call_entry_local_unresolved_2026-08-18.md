# Qualified `use prov` + `prov.f()` in entry module still fails codegen (GlobalLoad 'prov')
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED (2026-11-11, lane ne13) — the gate
`scripts/check/check-import-alias-codegen.shs` now PASSES all 5 forms on the
fresh seed; fixing commits cb5d19dd59c3 + 8cce7b626a28. See addendum.
**Filed:** 2026-08-18

Probe (fails on both the deployed seed and a fresh build WITH the
bare-assign-local minting fix, so it is independent of that change):

```
use prov
fn main():
    n = prov.provider_len("hello")   # -> GlobalLoad: unresolved identifier 'prov'
```

`check-import-alias-codegen.shs` PASSes its `qualified` fixture, so this shape
differs from the gated one (entry module + result assigned to a bare local).
Interpreter lane prints QUAL-OK. Discovered during rt_-alias lane-parity
probing (binary_runtime_hardening). Related:
`aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`.

## Scope correction (2026-08-18, later): qualified is broken in codegen GENERALLY — the 2026-08-10 "fix" was verified through silent fallback

With the strict-JIT fail-open fix now in the deployed binary, the alias gate's
own `qualified` fixture (`use target` + `target.base_get("x")` in a MID module
— no entry-module shape, no bare assignment) fails deterministically:
`codegen: 1 function body/bodies failed to compile: [mid_call]`, twice in a
row, no timeout. Previously this exact failure was UNTAGGED, so it silently
fell back to the interpreter, printed the expected output, and the gate
reported `ok qualified` — a false green. Every earlier PASS of
`check-import-alias-codegen.shs`'s qualified row (including 2026-08-10's
"qualified fixed" claim in
aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md) must be
re-read with this in mind: the interpreter produced the V:x, not the codegen
lane. The gate now correctly shows the defect; leave it RED per testing rules
(a correct check that fails is a legitimate artifact) until qualified binding
is actually implemented in the codegen lane.

## Addendum 2026-11-11 (lane ne13) — FIXED; the gate named above is GREEN

**Verification actually run** (worktree simple-p3-ne13-20261111, tip
c8b6d0ebe90e, fresh seed 46fe8f6b6def):

```
SIMPLE_BIN=$PWD/bin/simple sh scripts/check/check-import-alias-codegen.shs
#   ok    plain_sel
#   ok    alias_sel
#   ok    wildcard
#   ok    mod_alias
#   ok    qualified
# PASS -- 5 form(s) checked, all bind in the codegen lane   (exit 0)
```

`qualified` — the form this doc is about (`use target` + `target.base_get("x")`
compiled under SIMPLE_JIT_STRICT=1, so the codegen lane speaks instead of
silently falling back) — now prints V:x from the CODEGEN lane. The harness
sanity gate (plain_sel / wildcard / mod_alias controls) is green, so the
PASS measures the real codegen lane, not a dead-harness artifact.

**Fixing commits:** `cb5d19dd59c3` "fix(release): ... fix module-alias codegen"
(2026-09-20) for the qualified/module-alias binding, and `8cce7b626a28`
"fix(seed): imported function used as a value calls its body, not address 0"
(2026-10-20) for the alias-as-value shape. The gate's header comment now
records the fixed state (its own instruction: "if they pass, either the defect
was fixed (update this script) or the check is not measuring the codegen lane
at all" — the first branch; script header updated in this lane). `--expect-fail`
negative-control mode now reports FAIL by design, which is its designed
fixed-state signal.

Note: the AOT sibling `check-import-alias-aot.shs` was not re-run in this lane
(no entry-closure native builds are granted here — native-build Windows hang is
a known live defect); if it is wired into a lane that can AOT-build, re-run it
there before citing AOT coverage.

