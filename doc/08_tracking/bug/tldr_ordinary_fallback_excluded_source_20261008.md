# TLDR ordinary fallback can target source already excluded by the package route

Status: OPEN. Interim fail-closed guard applied; automatic source fallback incomplete.

The driver replaces its source inputs with `route.source_paths` before importing cached function headers. A body-required archive admission previously continued in ordinary mode without adding source back. The HIR resolver likewise declined mixed/namespace/generic imports, but that decline did not establish an available ordinary surface. Missing namespace surfaces could be silently ignored by the legacy module-only path.

Automatic archive-header admission remains gated by existing strict entry-only opt-in; ordinary warm archives retain their prior route behavior. A declined explicitly admitted-header import with no ordinary target surface now reports an error. Default header admission cannot be enabled until the planner fallback exists. Actual source surfaces continue through the ordinary resolver; supported function-only imports retain header admission. Strict diagnostics stay unchanged. Valid cached objects remain intact.

Required planner repair: classify full import demand (functions, types, namespace/glob, generic bodies, method bodies) before source exclusion; expand authorized source tasks once and reconcile their archive/action accounting. Reuse existing parsed surfaces and cached objects where compatible. Do not append arbitrary paths after route admission or silently mark archives sufficient for missing bodies.

Five executable resolver criteria plus four real consumer entrypoints are authored. Native archive-backed compilation, planner fallback and timing are UNRUN. A future complete fallback must compile the mixed/namespace/generic consumers with expected result42 instead of stopping at this guard.
