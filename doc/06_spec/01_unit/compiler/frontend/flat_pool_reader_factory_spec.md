# FlatPoolReader public static factory

Executable: test/01_unit/compiler/frontend/flat_pool_reader_factory_spec.spl
Shared actual controls: flat_pool_reader_factory_fixture.spl
Native entry: flat_pool_reader_factory_native.spl
Status: UNRUN. This manual is source documentation, not execution evidence.

The scenario calls the real public FlatPoolReader factories and mutable methods. It checks integer/length/text contents and cursor positions, preserves trusted legacy noncanonical integer acceptance, accepts a complete canonical frame, and rejects missing final newline, noncanonical integer spelling, trailing data, negative length and truncated length.

The BDD spec and explicit nonzero native entry call the same exported reason-returning helper. A successful native probe must print exactly PASS flat-pool-reader-factory with exit0 and empty stderr after a separately reviewed strict clean link. Neither a provider-only compile nor an empty BDD run qualifies these controls. Broader consumer diagnostics and compiler/lib/MCP/LSP checks remain unqualified.