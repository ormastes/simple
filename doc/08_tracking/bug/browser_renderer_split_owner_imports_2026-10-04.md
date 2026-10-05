# Browser renderer split modules omit existing owners

The completed early Phase4 build of source `9d484080c34c6e52ea001c5231c0f62bc0e383ea`
with Phase2 producer SHA-256 `0fce5d949d48b1a924c8131cc496ec191c8fce43033dbdc793386d819cc61e99`
records 25 HIR diagnostics in paint_layout, 17 in paint_raster and 12 in
decl_apply. The retained complete log SHA-256 is
`0850b659da9f5a612051ed073f9062414329818219bce1f96c3f044b6be01340`.
Only ten diagnostics per module were displayed; these are not test failures.

The split modules already depend on foundation/style/declarations, but their
explicit import lists omit existing helpers, budget state and constants used
in their bodies. Add those owner bindings, including direct box-shadow and
font-metric imports. The declaration helper imports retain the existing
declarations/decl_apply relationship. No function bodies, timeout policy,
shared-state ownership, visibility or renderer semantics change.

Four executable regression scenarios import all three affected modules and
exercise currentColor, sticky-auto declarations, paint dimension clamping and
visible overflow clipping. Native execution is UNRUN pending the repaired
Phase2 producer. Source checks cannot establish native compilation or RC
qualification. The complete Phase4 cohort remains 2544 HIR passes and 13
failures until rebuilt with actual evidence.
