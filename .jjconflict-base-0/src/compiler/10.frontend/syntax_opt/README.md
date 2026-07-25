# Syntax Optimization Group

This folder is the grouped home for **syntax-level optimization and normalization guidance**.

The implementation currently lives in [`../desugar/`](../desugar/), which is the active frontend
transformation pipeline. This folder exists so syntax optimization has an explicit, discoverable
grouping separate from MIR and backend optimizations.

Current syntax-stage transforms:

- `async/await` desugaring into generator/state-machine-oriented forms
- placeholder lambda rewriting into explicit closure forms
- collection pattern desugaring such as `x = x + [item] -> x.push(item)`
- spawn/resource/frame analyses that normalize or validate high-level syntax before lower stages

Level mapping used by the optimization guide:

- `basic`: semantic normalization and syntax rewrites
- `standard`: reserved for future optional syntax-level profitability transforms
- `aggressive`: reserved for future more expensive syntax-to-syntax rewrites

Notes:

- These transforms are currently treated as frontend normalization, not optional native-only tuning.
- MIR and native executable optimization levels are documented separately in
  [`doc/07_guide/compiler_optimization_levels.md`](../../../doc/07_guide/compiler_optimization_levels.md).
