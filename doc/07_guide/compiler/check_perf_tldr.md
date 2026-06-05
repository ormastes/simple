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
Self-check:      bin/simple build check
Bootstrap:       bin/simple build bootstrap
Size audit:      sh scripts/check/check-startup-size-performance-audit.shs

Optimize: val>var, iteration>recursion, typed List<T>, mode escalation.
Guide:    doc/07_guide/compiler/check_perf.md
```
