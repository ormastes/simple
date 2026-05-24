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

Next implementation candidates:

- Connect JIT execution-manager profile counters to `profile.hot_count` facts.
- Add hotspot-plan invalidation tests.
- Add representative benchmarks before making performance claims.
