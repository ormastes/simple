# Block and MIR optimizer facade owner gaps

Status: source candidate; native consumer qualification pending.

The retained 54f cache-facade API build fails during HIR lowering. Its 60
logged fatal events include 31 block-system failures, 27 MIR optimizer
failures, and two imported `ImplBlock` failures. These are not 60 independent
bugs. The imported Optional fix already present in C37 is a separate candidate
for the `ImplBlock` failures; ten repeated `LocalId` failures remain unclassified.

`compiler.blocks.__init__` attributes `init_blocks` to the registry despite
its definition being in `blocks/mod.spl`, which the same facade already
re-exports. Other advertised block names lack explicit terminal-owner routes.
The MIR optimizer facade likewise omits `MirPass` and four pipeline functions
already explicitly exported by `mir_opt/mir_opt/mod.spl`. The failing import
receipts name these package facades, rather than the declaration owners.

The correction removes the invalid duplicate registry export and supplies 26
explicit routes to existing public declarations. Six newly reachable block
providers use file-direct internal imports, preserving the requested owner.
This avoids exporting another 19 implementation dependencies from the package
facade, including a dangerous collision between helper `parse_json` and the
distinct utility `parse_json`. No implementation body, resolver algorithm,
scope cleanup, cache invalidation rule, or test assertion changes.

The six providers were absent from the earlier HIR progress inventory; closure
growth is therefore expected and must be measured. They have no top-level
mutable initialization declarations. Existing registry initialization remains
lazy. The old package facade already participates in a cycle through
`blocks/mod.spl`; new declaration routes and backreferences still require
actual duplicate/cycle and provider-identity qualification.

Static qualification verifies the 26 declarations and their pre-existing
public contracts, all canonical internal import targets, and unchanged bodies
in the six providers. This is not native correctness or performance evidence.
The actual eight-check cache facade fixture and its changed-expectation
negative control are reused unchanged from separate loader dependency
`9b3ff93cb77` (local cherry-pick `746d6fb5368`). C37 compiler construction alone
does not qualify the consumer closure or this patch.

Detailed evidence and owner tables:
`/home/yoon/dev/phase2-six-results-20261011/common-facade-correlation/`.
