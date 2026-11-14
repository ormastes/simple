# MIR transient owner field inventory

Source: `test/01_unit/compiler/mir/transient_owner_promotes_every_field_spec.spl`.
This hand-authored manual describes ten source-inventory scenarios; it is not generated runtime evidence.

| Coverage | Assertions |
|---|---|
| Source discovery | Sources are readable, relevant structs/methods exist, and extraction includes known late-added fields |
| MirLowering | Every declared field is an explicit root; historically omitted RTI and extern/default-literal roots remain covered |
| RTI and nested classes | Declared children of retained class owners are individually rooted |
| MirBuilder | Both mutable-reference writeback arrays are discovered; every declared builder child is an explicit root |

Comment-only roots and roots outside the promotion method do not count. The new builder check enumerates the declaration instead of maintaining a second fixed list; it also requires a nonempty list and explicitly recognizes both writeback arrays.

Related executable static gate: `scripts/check/check-mir-transient-scope-boundary.shs` passed once on this patch: 35 unconditional scanner fixtures and 18 production invariants. Added fixtures accept valid public forwarding declarations, delimit them at the next public function, and reject public owner forwarding that omits release. Existing private and malformed forwarding fixtures remain active.

The ten Simple scenarios and native lifetime probes are **UNEXECUTED** under the bugfix verification waiver. The static gate PASS is source-shape evidence only. No use-after-free reproduction, compiler bootstrap or performance result is claimed.
