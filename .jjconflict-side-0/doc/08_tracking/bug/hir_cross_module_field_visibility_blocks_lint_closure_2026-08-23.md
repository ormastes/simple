# Cross-module struct field/constructor visibility blocks the 140-module lint closure at step 2/6

Filed 2026-08-23 from the monomorphization lane, as a **measured negative
result**: it is what actually stops a real closure, and it is NOT what the
phase36 forecast predicted would stop it.

## What was run

```
native-build --source src/app/lint --entry-closure \
  --entry src/app/lint/main.spl --threads 4
```

worktree `/mnt/fast/wt-mono-1`, deployed seed
`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
`SIMPLE_TIMEOUT_SECONDS=0`, `SIMPLE_CACHE_SCOPE=mono1_lint_fix`.
**Closure size: 140 modules.**

## Result

`hir 140/140` completes, then rc=1 at **step 2/6** with **1512 HIR lowering
errors across 44 files**. Monomorphization is never reached: no `[mono]`
receipt is emitted, and `E-MONO-030/032/033` counts are all **zero**.

| class | count |
|---|---|
| ``field `X` is not visible from this module`` | 1238 |
| ``aggregate constructor `X` is not visible`` | 174 |
| `unresolved type` | 80 |
| `unresolved name` | 20 |

Top fields: `trimmed` 190, `line_num` 182, `byte_offset` 150, `line` 144,
`indent` 124, `results` 98. Top constructors: `SimdOpportunityWarning` 70,
`ProcessResult` 12, `LintDiag` 10, `Token` 8. Top files:
`src/lib/nogc_sync_mut/tooling/easy_fix/rules_lint.spl` 156,
`.../easy_fix/rules.spl` 148, `src/compiler/tools/lint/_LintMain/lint_checks.spl`
108.

## Mechanism (one confirmed instance)

`src/lib/nogc_sync_mut/tooling/easy_fix/rules_helpers.spl:12` declares

```
struct LineContext:
    ...
    trimmed: text          # no explicit visibility marker
```

and `rules_lint.spl` — a DIFFERENT module — reads `.trimmed` off a
`LineContext`. HIR rejects that read as not visible. So a plain, unmarked
struct field is treated as module-private, and every cross-module field read
on a shared struct fails. The `aggregate constructor` class is the same rule
applied to construction rather than field read (`ProcessResult` is exactly the
symbol the phase36 forecast's rung 1 hit on the 7-file `src/app/memstat`
closure, so this is the same defect at 20x the scale).

Not yet established, and deliberately not asserted: whether the intended rule
is "unmarked fields are public" (and the checker is wrong), or "unmarked
fields are private" (and 44 files need markers). That is a design call and is
why this is filed rather than patched.

## Why this matters to the generics/mono lane

The phase36 forecast ranked `E-MONO-033` as the CERTAIN, dominant blocker
immediately after HIR, expecting it "in the hundreds". On this closure that is
wrong in the strongest possible way: mono raises **zero** diagnostics because
**control never reaches it**. Cross-module visibility is the real next wall
for the lint closure, and it is an HIR-layer defect with no generics content
at all (`generic structs are not supported` appears **0** times).

Consequence for the mono fix landed at `75f554903ff`: it is proven at fixture
scale (closure size 1) and by call-site enumeration, but it remains
**unvalidated at real closure scale**, because no real closure currently gets
far enough to exercise it. Any claim that stage1 "now survives
monomorphization" is unsupported until a closure clears this wall.

## Also worth noting: the silent-abort symptom is gone

The forecast recorded this same lint closure exiting **rc=255 with ZERO
diagnostic output** and no receipt — its item 1, "undiagnosable as shipped".
It now exits rc=1 with 1512 clearly attributed diagnostics naming file, symbol
and reason. Whatever changed between those trees fixed the reporting defect;
the underlying failure was simply invisible before.

## Caveat on this run

The mono source was edited mid-run in this lane (a `Field`-arm experiment was
reverted while shards were live), so shards may have seen inconsistent
compiler source. The conclusion is unaffected: every one of the 1512 errors is
an HIR visibility/resolution error in files this lane never touched, and the
build died before monomorphization ran at all.
