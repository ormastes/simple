<!-- codex-design -->
# Optimization Plugin JIT Hotspot Tasks

Done in this slice:

- Research existing optimization plugin and JIT docs.
- Add local/domain research artifacts.
- Add feature/NFR requirements.
- Add architecture/detail design.
- Extend provider schema with `JitHotspot`.
- Add built-in JIT hotspot provider helper and runtime-hotspot predicate.
- Add unit coverage for required runtime facts and safe-deopt gating.
- Update guide, architecture, and spec docs.
- Connect tiered JIT profile counts to `profile.hot_count` facts.
- Add data-only hotspot plan and invalidation helpers.
- Add unit coverage for hotspot fact extraction, eligibility, and invalidation.
- Add representative hotspot planning benchmark and first measured evidence report.

Next implementation candidates:

- Thread `JitHotspotPlan` into the native execution manager once a concrete specialization provider consumes it.
- Add native backend specialization benchmarks after a concrete JIT hotspot provider consumes `JitHotspotPlan`.
