# Record array-element operators compare runtime handles

Status: native runtime RED; typed-provenance repair authored, not yet verified.

Admitted producer:699083c7f296812a3df4751b5606c78af989d6e918e0f8e349fd2be2d6b00971.
Its source snapshot4a55053825b5e1da186d6168136f5985afc1d6457dea3d27e31733387a4da3df
includes the first imported-owner repair. All1400 producer modules compiled,
sanity/capability admission passed, and its runtime capsule verified.

The two-module fixture compiles both modules with no failures. Native execution
passes the typed-parameter cases, then exits14 on `records[0] != records[1]`.
Values1 and11 are equal under the provider's custom modulo-ten __eq__ relation.
This compares individual record elements, not whole-array content equality.
Executable SHA256:`91eadd11021196d55cd46f4d9a129a62e99272ac167b3d042a358657f53bb2c9`.
Baseline sources are pinned in SCV snapshot
`scv-revision-v1-0092ea533119ae593797dfb26385826ff2b70477e0b2cdfed4c243ee015e11c9`.
Evidence is in `build/native_probe/imported-inequality-699083c7/`, including
compile.log, process.env, evidence.json, run.log and main-disassembly.txt.
The compile receipt is complete0, peak5657564KiB, quiescent1; run exit14.

Disassembly of the failing site calls rt_array_get, then directly executes
`cmp x19, x0` and returns14 on unequal handles. There is no __eq__ call at that
site. The MIR Struct-only gate misses a record element held in an i64 runtime
handle despite its declared Named record owner being available.

The candidate now admits exact current-function HIR record ownership as well
as a MIR Struct representation. Raw layout-name notes alone still cannot
classify a scalar. It retains distinct layout spelling for arithmetic result
metadata rather than substituting the qualified method identity. Six authored
MIR scenarios now cover demand/eager imports, same-name owner isolation, array
elements, ordinary scalar multiplication and provider-owned arithmetic. The
native fixture adds a scalar check and a second-field check on an addition
result. These latest sources remain UNRUN pending a rebuilt producer.

The separate store probe reached MIR197/197 with zero failures, then its extra
8GiB outer budget stopped it (exit88, peak8393008KiB, quiescent1). It produced
no executable and no runtime-accounting PASS. This was a session-imposed cap,
not a change to the canonical compiler's memory policy. Native qualification
of this known-failing candidate was stopped and caches retained. No Phase3
PASS or integration is established.
