# stage4 cranelift-direct lane regressed by flat-lane fixes (origin 4b79454)

**Date:** 2026-07-23
**Lane:** stage4 full-CLI binary, `native-build --backend cranelift` (cranelift-direct)
**Status:** OPEN — filed by the AOT probe campaign; regressing commits verified only on the flat/LLVM lanes

## Symptoms (origin-pure 4b7945435459, clean-cache stage4 rebuild)

Probe matrix on the campaign's probe set (probes in the campaign worktree; shapes inline below):

| probe | shape | expected | origin-pure result |
|---|---|---|---|
| probe_enum3 | match over enum w/ (text, i64?, text) payload, statement arms, interpolation | `v=payload` / `t=7 v=second` | `v=103915749287153` / `t=103915749292625 v=7` — text payloads print as raw heap handles AND binding order shuffled |
| probe_rich | `fn add(a: i64, b: i64) -> i64` + call | compiles | **SEGV (139) while compiling** |
| probe_enum6 | `fn classify(k: K) -> text` + match | compiles | **SEGV while compiling** |
| pm5 | `fn t() -> text: return "hi"` / `print(t())` | compiles | **SEGV while compiling** |
| pm6 | same + local binding | compiles | **SEGV while compiling** |
| trivJ / t2 / t7 | scalar/loop/multi-fn | green | green (unaffected) |

Baseline: at a4afc72a34a (batch 4) + campaign batch-5 WC fixes, the same probes were
9/11 fully correct with zero SEGVs (enum3 exact text output; rich compiled AND ran
correct). The SEGV class specifically hits every probe whose compile path touches a
function with parameters + declared return.

## Suspect commits (a4afc72..4b79454)

- **c902e5cf555** — "Str/Bool const-inline typing" + expr pre-dispatch global-read
  fallback: prime suspect for the enum-payload text corruption (payload text slots
  now render as handle decimals in interpolation; binding positions shuffled).
- **43ddb851702** — call-return-type registry ("Str-narrowed priority + cross-module
  pre-registered ret-type registry"): prime suspect for the compile-time SEGVs on
  parameterized/value-returning fns (the registry priority path runs exactly there).
- 642cdccfd0c (join normalization) and 4b794543545 (flat entry-closure, isel rename,
  ptrtoint statics) less likely but in range.

All four were verified via flat-lane/MCP repro chains (W80–W109); none were run
against the cranelift-direct probe lane. This is the same class as the campaign's
own rule: a lane-specific fix needs the other lane's probe matrix before landing.

## Repro

```
# stage4 build per campaign recipe (fixed seed + fresh runtime archives), then:
simple native-build probe_enum3.spl --backend cranelift -o /tmp/e3.bin && /tmp/e3.bin
simple native-build pm5.spl --backend cranelift -o /tmp/pm5.bin   # SEGVs
```

## Next

- Bisect the 4 commits on the cranelift-direct probe matrix (each is one stage4
  rebuild); fix forward on the regressing hunk(s) — do NOT revert the flat-lane
  wins, they are verified on their own lane.
- The campaign's batch-5 (value-position match/if result correctness) lands ON TOP
  of this regressed base: it strictly improves the lane (pm1/pm2/pm4 0 -> correct
  arm values) and does not touch the regressed behaviors.
