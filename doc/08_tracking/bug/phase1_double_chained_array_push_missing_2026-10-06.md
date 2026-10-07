# Phase1 double-chained array push missing

The old Linux seed sweep failed three provisional-Hello profile examples with method push not found on value of type array in nested call context. Direct single-chain controls pass. Two parsed-Simple regressions reproduce the missing push and append methods on double-chained array receivers.

Share the existing value-level array append operation between direct and chained dispatch. Arguments in chained dispatch are already evaluated; append their values without evaluating expressions again. Return a new array, preserving the original receiver and the established direct-method behavior, including the existing missing-argument Nil default.

Both double-chain regressions failed before the repair and passed afterward. They require a one-element original array to remain unchanged while the returned array grows to three elements. The four passing diagnostic controls were not re-executed. Enforcing watchdog evidence records exit 0, quiescent 1, peak 4748740 KiB, and maximum sample gap 4411 ms against the 5000 ms observation budget. Evidence is retained under /tmp/simple-nested-array-push-repair.

Verification of the original profile examples on a newly built seed remains pending. The active canonical seed build has its source pinned before this repair; its source was preserved. These focused interpreter regressions do not admit Phase2 or qualify the whole seed suite.
