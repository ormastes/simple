# Check Perf TL;DR

```
┌─────────────────────────────────────────────────────┐
│              Simple Execution Modes                  │
├──────────────┬──────────────┬───────────────────────┤
│ Interpreter  │  SMF Loader  │  Native (AOT)         │
│ simple       │  compile →   │  compile --native →   │
│  file.spl    │  simple .smf │  ./binary             │
├──────────────┼──────────────┼───────────────────────┤
│ fast start   │  ~2-5x       │  C-level throughput   │
│ slow run     │  dispatch    │  slow compile step    │
│ dev cycle    │  staging     │  production           │
└──────────────┴──────────────┴───────────────────────┘

Cross-language:  sh scripts/check/check-cross-language-perf.shs
GUI baseline:    sh scripts/check/check-gtk-gui-size-speed-baseline.shs
Size audit:      sh scripts/check/check-startup-size-performance-audit.shs
Self-check:      bin/simple build check
Bootstrap:       bin/simple build bootstrap

Optimize: val>var, iteration>recursion, typed List<T>, mode escalation.
Guide:    doc/07_guide/compiler/check_perf.md
```
