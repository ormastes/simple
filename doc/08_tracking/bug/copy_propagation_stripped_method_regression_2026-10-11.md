# Copy propagation stripped method names regressed

**Bug:** `copy_propagation_stripped_method_regression_2026-10-11`
**Status:** FIXED in the linked release PR; authoritative test DB reconciliation pending.
**Requirement:** REQ-COPYPROP-DECLARED-NAME — internal calls resolve the actual declared helper while preserving operands and destinations.

Pure-Simple `CopyPropagation` declares `copypropagation_propagate_operand`, `copypropagation_propagate_instruction` and `copypropagation_propagate_terminator`. Fifteen internal calls used the stripped names instead. An actual Stage1 regression execution failed with `semantic: method propagate_operand not found on type CopyPropagation`. This prevented the first optimizer unwind-destination example from reaching its assertions; the other three examples passed. That original four-case feature stopped at its three-attempt limit.

Commit `d6fce96e530246439b87b4d785560b1cbe0641cc` had already corrected these names and documented executed controls showing that both `fn` and `me` use their declared name without implicit type-prefix stripping. A later source snapshot reintroduced the stripped calls. Current release `95c12f073ffefa99ac774264beeedd68a47e7676` and the captured optimizer source had identical bytes before this repair.

The repair restores exactly fifteen declared-name call spellings. It leaves declarations, pass dispatch, copy-chain policy, exception destinations, memory behavior and loop structure unchanged. Existing pass quarantine is outside this change. No global name-prefix stripping or alternate optimizer implementation is introduced.

New prevention spec: `test/01_unit/compiler/mir_opt/copy_propagation_declared_methods_spec.spl`. One example calls instruction propagation and verifies both a load's destination and its pointer local. The second calls return propagation and verifies the retained return local. These are independent of the exhausted four-case sequence and exercise two other callers of the same named helper. Both examples were authored before the repair: baseline **2 executed, 0 passed, 2 failed**, both with the missing-method error; repaired **2 executed, 2 passed, 0 failed**. Neither attempt skipped cases or changed assertions.

Evidence is retained at `build/sol-phase1-unicode-release-20261011/seven-regression/declared-method-repair/{baseline,fixed}/CASE_REVIEW.json` and each preserved `child-artifacts/` directory. Each run authenticated a quiescent Windows Job, verified 207 source files plus ten seed/helper/control pins before and after, and stayed within the 1-GiB/120-second cap. Peak RSS was 432032 KiB before and 432600 KiB after.

Runtime provenance: immutable Rust bootstrap seed SHA-256 `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`, explicitly routed to the Rust Stage1 test runner. The private capture retains a Windows-only section specialization because this stale seed cannot parse current block-form `@when`; that private workaround is excluded from the production commit. This evidence qualifies the named Stage1 regression scope only. Pure-Simple full-suite, native products and Phase2 are not qualified by these results.

The actual repair commit is the commit introducing this report; its release PR supplies the immutable commit and merge linkage. No historical test database is treated as current execution evidence.
