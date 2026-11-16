# Staged target-bound entry for existing mutable HIR

The accepted immutable HIR plan requires applying target context before target-sensitive MIR reads. This bounded increment adds `UnfrozenMirModuleInputV1`, carrying the actual module and requested context together. It does not create `HirSnapshot` or `TargetHIR` authority.

`MirLowering.lower_unfrozen_module_v1` rejects missing/placeholder arch/OS/ABI/backend, then compares the complete common thirteen-field identity against both the current context and constructor-bound identity before invoking trace/cfg/module lowering. Provider/archive arguments pass through unchanged. A defaulted field appended to MirLowering preserves earlier field order; its constructor sets the binding once. Direct legacy construction with an empty binding cannot enter this route. Public mutable fields remain a compatibility limitation, not a security boundary against deliberate mutation of the binding itself.

Only the explicit-target verification call producer migrates, after existing source-environment admission. The default producer retains its intentionally unknown-context compatibility path. Existing source ownership, call capture and receipt finalization remain in place. No ambient host resolution is added and no rollout flag/default is changed. Strict-entry errors are returned as Results before MIR effects; existing lowerer diagnostics remain the caller's responsibility after successful entry.

Remaining: deep immutable ownership, snapshot/region proof and lifetime pins, frozen resolution overlay authority, mandatory migration of other driver/bootstrap/archive/plugin entries, and native Stage 3/4 qualification. Raw lower_module remains available; this is not the final TargetHIR-only API milestone. The binding stores one framed context per lowerer; construction overhead is unmeasured and must be profiled before broad rollout.

Evidence: seven authored behavioral scenarios, source review and the static boundary gate described below. Runtime, bootstrap, cache and performance qualification are UNEXECUTED. Feature destination is the integration branch, not release/1.0.0 bugfix landing.

The placeholder gate deliberately does not introduce a second supported-target vocabulary or prove platform/ABI admission. The common normalizer remains authoritative; native is a valid backend. Constructor binding is included in transient owner root promotion.

Historical boundary gate: the initial feature parent `16e6180752d3e75cacb335641451cc6d44607667` declared MirBuilder mut_ref_param_ptrs/mut_ref_param_values without their promotion roots, and its public SFFI helper was not recognized by the old scanner. Source comparison confirmed these failures predated this feature; its own new binding root was present.

Current boundary evidence: after rebasing onto release parent `1a90b730` containing repair PR #9223, one run of `sh scripts/check/check-mir-transient-scope-boundary.shs` passed its 35 unconditional scanner fixtures and all 18 source invariants, including this feature's binding root. The earlier static failures are resolved by that parent repair. This is not native lifetime or feature qualification. Complete tuple/ABI compatibility validation remains a separate common-owner task.
