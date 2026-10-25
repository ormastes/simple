# Retained HIR bootstrap processes v1 — TLDR

Status: approved architecture; authored source/tests UNRUN. No qualified self-hosted test CLI is available. Default Cranelift >=10 actual object-codegen overlap remains required, not claimed.

Reuse selective retained-HIR bodies/declarations, existing physical-emission schedule and bounded `run_ledger_shards`; no new scheduler, MIR codec, fork bridge or seed. Each child owns one body/MIR/object and private writable cache. Parent validates immutable fragments and commits ordered results; any original HIR/worker failure forbids link.

Bootstrap admission adds exact source/context/physical/producer identities, entry ownership and Stage4/post-chain semantics plus three actual owner snapshots: function/default, callable/static, enum/composite. Publish bounded canonical SDN with actual owner digests; prove reconstructed state matches serial owners before enabling bootstrap semantics. Physical manifest binds mono placements and context generation.

Preserve unsupported-state and SOURCE-seal guards. Keep the full original READY/HIR_FAILED/EXCLUDED/BLOCKED inventory; schedule only READY rows whose providers are READY. Charge parent metadata, exporter, worker/tool tree, pending outputs and disk against measured admission caps. Ten requested jobs is no proof of ten admitted workers or overlapping object compilation.

Owners: A registry transport; B context/inventory and acceptance; C explicit bootstrap worker semantics; D private caches/parent adoption. Root merges; independent Astra reviews exact integration. See [full design](native_mir_selective_bootstrap_process_v1.md) for interfaces, paths and acceptance.
