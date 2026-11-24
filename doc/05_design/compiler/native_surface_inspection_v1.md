# Read-only native surface inspection

`inspect-native-surfaces` is a bootstrap diagnostic command, not a compile mode.
It accepts the canonical native source/entry/target/cache flags plus one or two
`--module` selectors, one `--item`, and `--diagnostic-root build/verify`.
It rejects native output flags and worker/shard contexts.
An omitted target follows the unchanged canonical factory, including its raw
empty host-default value. The record distinguishes the CLI spelling, raw target
before source loading, and implicit ambient/default versus explicit CLI policy;
it never replaces the empty value with a guessed host triple.

The coordinator publishes source authority and the canonical immutable closure,
then admits that closure through the existing capsule handoff owner. The focused
CLI shares all target/environment setup and driver construction with native-build.
The observer runs canonical source loading and configured parsing/surface freezing,
then stops before HIR bodies, MIR, and codegen. Environment restoration is shared
with the ordinary focused route, and the coordinator clears the handoff on exit.

The checked SDN identifies its `prebody-frozen-query` capture point, diagnostic-only
status, absent compile admission, registry generation, source closure identity,
target/policy, actual frontend session ID, and selected physical indices. Selected
modules retain callable names, import offsets/items/targets and resolver probes,
export routes, selected origin and the normal re-export walk result. The walk uses
a fresh private lowering/query owner. The existing session/scope checked name-index
read cache may be populated; neither query memoization nor that cache changes the
retained registry or materializes declarations. Target receipts and source hashes are included
when retained; absence is explicit. A prebody query is not proof of failing-body
context equivalence.

Missing selectors or import targets are substantive observed outcomes. Malformed
selectors, failed load/parse/freeze, incomplete projections and exceeded bounds
fail the diagnostic. Limits: two selected modules, 512 imports/module, 4096 import
items/export routes, 1024 callable names, 128 resolver probes/import, 512 target
decisions, 512 KiB/module and 1 MiB total. Publication failure cannot count a completed observation.
A canonical physically checked root owns a fresh private temporary directory.
The fixed `inspection.sdn` is published exclusively without replacement, with
physical parent rechecks and bounded no-follow digest readback; existing evidence
is never deleted. Only successful publication prints the actual fresh path.
The output never creates native-build receipts, stage admission or guest proof.

The focused regression parses a Windows-local/POSIX-import conditional facade,
freezes its Linux surfaces, observes the real bare-export walker, and checks a
missing target separately. Specs are authored but unexecuted until an admitted
compiler runs them. The first fresh producer must inspect the retained SDK closure;
the final native cycle remains reserved for a reviewed source fix.
