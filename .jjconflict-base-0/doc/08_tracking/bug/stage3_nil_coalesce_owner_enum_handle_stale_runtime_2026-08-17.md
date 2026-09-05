# Stage 3 trace showed `??` on `text?` yielding `<enum@0x...>` — not reproducible from the current tree

- **Status:** OPEN, but the current-tree source is **exonerated by measurement**.
  Most likely a **stale linked runtime** in the stage-3 lane, not a source defect.
- **Not fixed.** Nothing was changed for this record.

## The observation (from the stage-3 diagnostic trace, 2026-08-17)

62 trace lines from the `[HIR-PAYLOAD-LOOKUP]` probe
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1374`) carried
`owner=<enum@0x1e1b70fa0>`-style values. `existing_owner` is
`symbol.defining_module ?? ""` and `defining_module` is declared `text?`, so a
raw pointer rendered as `<enum@0x...>` in a `text` field means `??` returned an
enum **handle** instead of the unwrapped payload — the same signature family as
`<value:0x1800000007>`, `0xfffffffffffffcf7`, and `1337030607`.

That is the `??`-on-Option defect that `ae07aaa29109` was supposed to close by
gating `rt_unwrap_or_self` on `rt_enum_id(value) == 1 && rt_enum_discriminant(value) >= 0`
(`src/runtime/runtime_native.c:4022`).

## Which of the two candidate explanations holds — measured

The two candidates were (A) the stage-3 lane's linked runtime archive predates
`ae07aaa29109` (the bootstrap wrapper runs "seed/runtime reuse only; cargo
disabled"), or (B) the gate is insufficient for this shape — a present
`text?` Some being boxed with a non-canonical enum id, so `rt_enum_id != 1`
and the gate declines to unwrap.

**(B) is contradicted by measurement.** A native ELF built today from the
current tree, via the same Rust native-build handler the bootstrap uses
(`SIMPLE_NATIVE_BUILD_RUST=1 … --backend cranelift`), on exactly this shape —
`??` applied to a `text?` **class field**, both Some and nil:

```
SOME_OWNER=[mod.one]
NONE_OWNER=[]
run_rc=0
```

Both arms correct. The gate handles a present `text?` field, so the current
source does not exhibit the defect. That leaves **(A), a stale linked runtime in
the stage-3 lane**, as the surviving explanation. Confirming (A) directly
requires identifying the archive the stage-3 lane actually linked and comparing
it against `ae07aaa29109` — **not done here**; the lane's working tree was
off-limits (a replay was in flight).

## A third candidate, untested

The 62 lines are the *same* probe lines that the `Dict.clear()` defect
(`stage3_dict_clear_no_dict_branch_in_rt_clear_2026-08-17.md`) explains: the
`symbol` record they print was fetched via a **stale id**, so it may have been a
foreign record whose `defining_module` slot held an unrelated value that `??`
then passed through faithfully. On that reading `??` is not at fault at all.
**No shared root cause is asserted** — this is a hypothesis, not a
demonstration, and it is listed only so the next reader re-checks these 62 lines
after the `Dict.clear()` fix rather than assuming they are independent.

## Next step

Re-run the stage-3 diagnostic replay with the `Dict.clear()` fix in place and
count the `owner=<enum@0x` lines. If they survive, identify the linked runtime
archive's provenance (candidate A). If they vanish, they were downstream of the
stale-id defect (candidate C).

## Related

- `scripts/check/check-nil-coalesce-option-gate.shs` — the behavioural guard for
  the gate this record concerns. It was not modified.
- `doc/08_tracking/bug/stage3_nil_coalesce_unwraps_user_enum_payload_2026-08-08.md`

## Re-verified 2026-08-17 (still OPEN — current tree re-exonerated, lane not reachable)

binary identity: `readlink -f bin/simple` = `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`; `stat -c '%s %y'` = `59537240 2026-08-17 12:58:51.339525019 +0000`

The behavioural guard was RUN, not merely cited, and its ablation arm proves it
is not vacuous:

```
$ (ulimit -v 8000000; timeout 900 sh scripts/check/check-nil-coalesce-option-gate.shs)
[selftest][RED] case1 VERDICT: FAIL - user enum unwrapped to PAYLOAD (defect reproduced)
[selftest] OK — ablated arm reproduces the defect (rc=1), fixed arm checked below
core_values.spl: enum_id gate present
[GREEN] case1 user-enum:   enum_id=7 disc=0 coalesced=0x64ea765332a1   (pass-through)
[GREEN] case2 option-some: enum_id=1 disc=0 payload=0x7 coalesced=0x7  (unwrapped)
PASS — 3 case(s) checked, user enums pass through and canonical Option still unwraps
rc=0
```

The gate is present in the current tree (`rt_unwrap_or_self`,
`src/runtime/runtime_native.c:4042`). Candidate (B) stays refuted.

Still OPEN for the reason the record already states: candidates (A) stale linked
runtime in the stage-3 lane and (C) downstream-of-stale-id can only be decided by
re-running the stage-3 replay, and a bootstrap was explicitly out of scope for
this session. Nothing was changed for this record.
