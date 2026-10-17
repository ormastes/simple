# MIR physical owners and feed identity

Authored manual for `test/01_unit/compiler/driver/mir_physical_owners_spec.spl`; not generated execution evidence. Status: TEST_BLOCKED pending an admitted producer.

The production planner retains one representative per canonical physical owner in admitted inventory order. Existing scenarios exercise std/lib aliases in either order, changed content, conflicting paths or owners, distinct basenames, malformed inventory shapes and invalid content identities.

The added production identity predicate has six scenarios and 14 assertions:

| Scenario | Expected result |
|---|---|
| Actual feed equals the complete inventory order | Identity; preserve feed |
| Same-size feed has reversed owners | Refuse identity |
| Feed omits or adds an owner | Refuse identity |
| Selected indices filter the inventory, including a retained prefix | Refuse identity |
| Indices reorder, duplicate, are negative or exceed inventory bounds | Refuse identity |
| Canonical std/lib owners agree; empty or wrong owners do not | Accept only matching nonempty canonical owners |

The caller extracts `.name` directly from each retained context feed element and invokes this predicate before changing the feed. Valid identity does not reread the HIR dictionary or rebuild the module array. Nonidentity continues through the existing rebuild; that path's separately recorded erased-read issue remains open.

There are 14 source-authored scenarios in the full spec. Runtime counts, native behavior, generated-manual output and bootstrap admission are unverified. The source predicates do not establish a repair for the captured p2_add access violation.
