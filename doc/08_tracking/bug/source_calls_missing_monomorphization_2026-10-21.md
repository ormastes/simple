# Source-call inventory rejected static generic programs before specialization

Status: source implementation and authored regressions pending independent production review; all runtime tests UNRUN.

The prior `source_calls_from_source_v1` route lowered HIR directly into resolved-call capture. The existing capture owner correctly rejected open generic declarations. Merely inserting the canonical pass was insufficient: specialized symbols were registered with nil signatures, and canonical substitution/request rewriting omitted retained parameter defaults. G7 already traversed defaults, so a default-only generic call could remain unresolved.

The source repair connects one invocation-owned canonical pass, restores exact specialized declaration signature transport, rewrites/substitutes defaults through the existing engine and requires clean G7 before unchanged capture/finalization. Ordinary compiler policy stays unchanged. Scope is one self-contained module; unsupported imports/transforms/calls and unused retained templates refuse honestly.

Tests exercise real source→HIR→mono→G7→MIR bindings, final declaration body/signature hashes, defaults and evaluation flow, fresh input ownership, budgets, failure isolation and regular-file command inventories. Source prediction is RED at the previous open-template gate; no observed runtime RED/PASS is claimed. External reviewed prerequisites and immutable before/after/provider/schema pins accompany the packet.
