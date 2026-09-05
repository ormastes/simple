<!-- codex-research -->
# Simple Optimization Architecture Roadmap Domain Research

Date: 2026-06-01

Scope: persistent profile, PGO/BOLT, and runtime-feedback concepts for
`doc/01_research/compiler/optimization/perf/simple_optimization_architecture_roadmap_2026-06-01.md`.

## Sources Checked

- LLVM profile-guided optimization guide:
  `https://llvm.org/docs/HowToBuildWithPGO.html`
- LLVM advanced build configuration guide:
  `https://llvm.org/docs/AdvancedBuilds.html`
- LLVM BOLT README:
  `https://github.com/llvm/llvm-project/blob/main/bolt/README.md`

An OpenJDK HotSpot runtime overview fetch was blocked by the upstream site, so
this document uses the local roadmap's HotSpot framing only as prior art and
does not claim fresh OpenJDK-source evidence.

## Findings

### Profile-Guided Optimization Is Multi-Stage

LLVM's PGO documentation treats profile-guided builds as a staged loop:
instrument, run representative workloads, merge profile data, then rebuild with
profile use. Simple's `.sprof` lane should mirror that shape instead of loading
runtime profiles implicitly in every command.

Implication for Simple:
- `.sprof` writes should be explicit or enabled by a profile mode;
- profile use should be opt-in for build/optimize flows;
- benchmark evidence must name the workload that generated the profile.

### Profile Data Needs Version and Workload Context

LLVM's PGO flow assumes the profile is tied to the instrumented binary and the
workload that exercised it. Reusing stale or mismatched data can mislead later
optimization passes.

Implication for Simple:
- `.sprof` records need schema version, producer version, module identity, and
  workload/source metadata;
- migration must distinguish exact reuse from advisory reuse;
- incompatible records should be ignored with diagnostics.

### BOLT Is Post-Link and Evidence-Driven

The LLVM BOLT README frames BOLT as a post-link binary optimizer that consumes
execution-profile information to improve already linked binaries. That aligns
with the roadmap's separation between runtime `.sprof`, LLVM PGO, and BOLT:
they are related feedback systems but should not share one unchecked data path.

Implication for Simple:
- BOLT integration belongs after native artifacts exist;
- BOLT evidence should be stored as a report or optimize-app input, not as a
  replacement for MIR/JIT safety facts;
- binary optimization should remain downstream from semantic correctness tests.

### Hot Runtime Feedback Still Needs Guard Facts

The local roadmap already requires typed-MIR and safe-deoptimization facts for
JIT hotspot decisions. External PGO/BOLT practice reinforces the same boundary:
profile data is evidence, not proof of semantic safety.

Implication for Simple:
- `.sprof` records may raise priority or select candidates;
- optimizer providers must still require typed facts and safe fallback;
- profile migration confidence must not bypass deoptimization gates.

## Requirement Pressure

The domain research supports a schema-first or measured-startup path before a
full persistent-profile implementation:

- define versioned `.sprof` records before runtime writes;
- keep profile loading opt-in;
- verify no hot-request full-tree scan, shell-out, or repeated profile reread;
- require workload labels for any claimed speedup;
- keep BOLT/PGO integration downstream from semantic and profile-compatibility
  checks.
