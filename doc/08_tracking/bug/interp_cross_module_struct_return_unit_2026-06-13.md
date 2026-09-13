# SUPERSEDED — was misattributed

## Closed 2026-09-13 — Stale: superseded, the diagnosis in the title was wrong

- **inferred**: this entry is already self-marked SUPERSEDED — there is no cross-module struct-return-Unit defect. The real defect is the `unit` parameter/keyword collision, tracked canonically in `interp_unit_param_keyword_collision_2026-06-13.md`, which remains OPEN.
- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): a cross-module struct return works — an imported-const/cross-module probe and the canonical entry's own `unit`-renamed proof both behave correctly; only the `unit`-named parameter still fails, confirming the misattribution.
- Nothing to fix here; the workaround (`unit`->`unit_label` in bench code) landed in June.

This bug was filed as "struct returned from imported module resolves as `Unit`" and blamed
cross-module struct ABI. **That diagnosis was wrong.**

Verified root cause: a parameter named `unit` collides with the `Unit` keyword token in the seed
parser. The failing case (`make_bench_result`) merely had a `unit: text` parameter; after renaming
it, the struct returns across modules correctly (proof printed `value=42` / `unit=ops`).

→ See the canonical bug: **[interp_unit_param_keyword_collision_2026-06-13.md](interp_unit_param_keyword_collision_2026-06-13.md)**

Status: CLOSED 2026-09-13 (stale, superseded). Originally: workaround landed (rename `unit`→`unit_label` in bench code); general seed fix open
pending authorization.
