# SUPERSEDED — was misattributed

This bug was filed as "struct returned from imported module resolves as `Unit`" and blamed
cross-module struct ABI. **That diagnosis was wrong.**

Verified root cause: a parameter named `unit` collides with the `Unit` keyword token in the seed
parser. The failing case (`make_bench_result`) merely had a `unit: text` parameter; after renaming
it, the struct returns across modules correctly (proof printed `value=42` / `unit=ops`).

→ See the canonical bug: **[interp_unit_param_keyword_collision_2026-06-13.md](interp_unit_param_keyword_collision_2026-06-13.md)**

Status: workaround landed (rename `unit`→`unit_label` in bench code); general seed fix open
pending authorization.
