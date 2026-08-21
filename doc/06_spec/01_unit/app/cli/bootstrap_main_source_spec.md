# Bootstrap main source

Mirror of `test/01_unit/app/cli/bootstrap_main_source_spec.spl`.

This source-contract suite checks bootstrap command dispatch, the narrow exported operation set, canonical Stage3/Stage4 routing, entry-closure propagation, rejection of removed runtime bundles, SMF compilation, closure/import resolution, parser-sensitive bootstrap inputs, canonical address helpers, and the ban on the historical `Map.new()`/`Dict.new()` initializer bug.

The assertions inspect repository source and fixtures. They are executable SSpec checks, but they do not by themselves execute a complete bootstrap or prove a produced binary boots.
