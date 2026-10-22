# Repeated contributors in the stale-snapshot guard

The required CI run for source `d9325632b89ac99840b899bfd30eb6e620ad52a2` passed thirteen rows, then terminated the full 182-commit stale-snapshot guard at its 240-second tier budget. That row has no complete verdict and is not PASS.

The guard now memoizes immutable contributor parents and scoped file lists within one scan. Each current commit still gets its original changed-file, surviving-contribution, loss, revert, rename and threshold checks. Every requested commit and the original forty-parent window remain in scope. Cache readiness is published only after checked writes, and failed reads/copies stop the scan with ERROR before publishing completed counts.

The corrected candidate passed twelve selftest groups, including a real overlapping-window clobber and failed copy/read/incomplete-pair controls, four exact line-ending cases, and one real commit scan. A preliminary 171-commit scan was interrupted to repair a review finding; it has no complete verdict. Whole-range timing and required remote CI remain pending. Independent source review found no remaining P0/P1 in the corrected memo.
