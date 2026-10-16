# FlatPoolReader public static factory

Executable: test/01_unit/compiler/frontend/flat_pool_reader_factory_spec.spl
Shared actual controls: flat_pool_reader_factory_fixture.spl
Native entry: flat_pool_reader_factory_native.spl
Status: focused shared native controls PASS on 2026-10-17; BDD execution and broader gates UNRUN. Native evidence is recorded below.

The scenario calls the real public FlatPoolReader factories and mutable methods. It checks integer/length/text contents and cursor positions, preserves trusted legacy noncanonical integer acceptance, accepts a complete canonical frame, and rejects missing final newline, noncanonical integer spelling, trailing data, negative length and truncated length.

The BDD spec and explicit nonzero native entry call the same exported reason-returning helper. A successful native probe must print exactly PASS flat-pool-reader-factory with exit0 and empty stderr after a separately reviewed strict clean link. Neither a provider-only compile nor an empty BDD run qualifies these controls. Broader consumer diagnostics and compiler/lib/MCP/LSP checks remain unqualified.
## Focused native qualification — 2026-10-17

Tested frozen source6cbcb6af476a719e1f77e31c01c40bbf93adb50b, exact0CD6 producer. Cycle1/3 built selected8-module parse closure with18/18 parse workers and10/10 HIR workers, no reported failures;6 actual selected SPL objects/capsules included the genuine provider, shared fixture and native entry. The separately reviewed strict link used those6objects,38 unchanged own-D9 C objects under391 current source/header/compiler hash proofs, /MD canonical entry and zero actual module-init roots. Link exit0/log0 with no FORCE/IGNORE; strict executable SHA2565E07DEDC2ECC0388A815DBACAB4B4640AE15CA3FF5D0A1C02DDDA068778DED79.

Its authorized FIRST AND ONLY execution PASSED: exit0, exact `PASS flat-pool-reader-factory` plus newline (30bytes), stderr0, no timeout, elapsed0.0261462seconds, unchanged pre/post executable hash. The actual map contains new, new_canonical, next_i64, next_len, decode_text, finish_canonical_frame, shared controls and main from the genuine selected objects. Exclusive invocation ledger, raw outputs and receipts are retained externally under flat-pool-reader-static-factory-native-cycle1/strict-link. No green run repeated; scoped factory/cursor qualification converged in cycle1.

This qualifies the actual public factory and shared cursor/trusted-versus-canonical denial controls. BDD execution and broader61consumer diagnostics, compiler/lib/MCP/LSP checks and compiler admission remain UNRUN. No all-consumer fix, deployment, Phase3 completion or merge is claimed. Source guard/manual evidence remains distinct from runtime evidence.