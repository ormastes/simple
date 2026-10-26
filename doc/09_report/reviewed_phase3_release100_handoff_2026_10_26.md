# Reviewed Phase3 sharing handoff — 2026-10-26

Base: release/1.0.0 `d1dcfaa19c09dd0ca804946439c9f76e4c605736`.
Reviewed donor branch: `0db0889e119cf6dfe0c171879e91dc065af1f591`.
This is a bounded source-sharing reconciliation, not a broad branch merge,
compiler generation, test run, performance result or full acceptance PASS.

## Included self-contained source

| Donor | Files/decision |
|---|---|
| #4863 `92dd5a3b9038` | `35.semantics/rt_criticality.spl`, `rt_criticality_validation.spl`, original differential spec and bug record. Invocation-local empty-capability analysis and ordered claim-name index. The target has no bounded trace helper; retain its untraced entry rather than adding unrelated donor progress calls. HAL and nonempty capability routes remain unchanged. |
| #4886 `0db0889e119c` | `50.mir/_MirLowering/module_lowering.spl`, two added qualified-default metadata controls and appended existing bug provenance. Preserve target parameter signatures, both field-index ambiguity guards, repository logic and value semantics. Only missing qualified default field-order registration and its two production callsites are added. |

## Equivalent/newer target implementations preserved

- #4869 `d571e0175cd8`: target already visits actual scalar symbol keys instead
  of the high-water range, explicitly accounting for mono IDs at2^50. Preserve
  that implementation rather than replacing its traversal with our sorted
  filtered helper or restoring a dense loop.
- #4883 `6555a6e033dd`: original #4856 named-type suffix index and archive
  invalidation already exist; the target archive hydration file is identical.
- #4884 `15918c274d86`: target parse shards call the shared native-worker
  admission helper, which already uses #4855 canonical selectors. Preserve the
  broader existing release worker route and strict inherited identity checks.
- #4853 P2 HIR store/lowering helpers and P3 MIR store are already identical;
  newer release driver/P4/P6/runtime semantics are not overwritten wholesale.
- #4886 parameter owner handling and field-index ambiguity guards already
  match or exceed the original repair; no target function-lowering delta.

## Dependency gaps held rather than silently imported

The target lacks the older SOURCE runtime headers/provider and compiler
request/context/account foundations. #4858's pure rebasing implementation itself
imports absent request-budget/type-check/canonical-enum-account owners. It is
not dependency-complete on this release merely because it was complete on the
donor. Its temporary integration was removed before the final source snapshot.

Accordingly #4857/#4858/#4860/#4861/#4866/#4871/#4872/#4874/#4877 require an
explicit reviewed older-foundation closure before they can be transferred as
coherent features. This handoff does not treat their absence as completed work.
No unlanded archive/factory/replay/backend/native/nullable WIP, rejected cache815,
new default or go-to-end policy is imported.

#4853 allocation-claim hardening is not identical to the target's older
session runtime. It needs a separate reviewed semantic adaptation preserving
release sharded/fork/RC registries; copying the donor's old runtime files is
unsafe. #4881 similarly needs adaptation to the target's newer MODULE_OWNED /
SIG_OWNER Cranelift cleanup instead of importing exposed-handle/readonly-word
dependencies. These remain explicit sharing gaps unless separately reviewed.

## Evidence and stop boundary

No tests, compiler/native builds, binaries or live process changes were run.
Current executable/compiler/native/paired performance checks are UNRUN.
Historical donor Rust/native passes retain only their original source/runtime
identities. The frozen Phase3 attempt6 ended at deadline with0 emitted objects;
the unanswered extra-attempt exception grants no new launch. WIP/checkpoints and
compatible caches remain preserved. A shared-source landing is not full SOURCE,
SSpec, compiler/Phase3 or release qualification.
