
## Run F: braced-import hypothesis also refuted — the source-edit avenue is CLOSED

| run | hypothesis tested | site | count |
|---|---|---|---|
| A | (baseline) | `compile_specialized_template` | **6** |
| B | omitted Optional field (`entry_point`) | `_default` | 2 |
| C | `-> text` returning `Ok(CompiledUnit(...))` | `_release` | 2 |
| D | static-method vs re-exported free-fn constructor | `_default` | 2 |
| E | dead-copy guard at `remember_local_hir_type` | `compile_specialized_template` | 2 |
| F | unbraced `use a.b.C` vs braced `use a.b.{C}` | `_release` | 2 |

**Six runs. Five distinct, individually-plausible hypotheses. The count has not
moved off 2 since run B.** Only the very first drop (6 -> 2) was ever real.

Run F is worth its own note because the reasoning was the best of the five: it
explained a detail the others ignored — *why the fatal names a FUNCTION rather
than a statement*. `compile_specialized_template` is a stub whose every pipeline
step is commented out, so its parameters are unused; but lowering the SIGNATURE
still lowers each parameter type, which is why all three wrappers (identical
parameter lists) are interchangeable victims. Two of those six types
(`DiContainer`, `AopWeaver`) used the rare unbraced member-import form — 86
occurrences tree-wide against 5073 braced. Bracing them changed nothing.

The braced form is retained as convention normalisation, explicitly NOT as a fix.

### Conclusion: stop editing source against this

Five hypotheses at ~55 minutes per run produced **one bit** of information. Every
edit was an avoidance edit at a victim site; none touched the producer, because
the producer is the ABI itself. Continuing to guess at candidate crossings has
negative expected value.

**The next action must be the sibling doc's second-read tag probe** — read the
HirType tag twice across a suspect boundary and compare — which distinguishes
"dead copy minted in flight" from "use-after-free of the original" in ONE
instrumented run. Build the instrument before touching source again.
