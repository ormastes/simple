# Item 6 SCC archive input grouping candidate

Status: SOURCE CANDIDATE. No native runtime or paired p95/RSS qualification.

The SCC archive publisher previously scanned every input once for each
required package. For N inputs spread across P packages, its grouping loop
performed O(P*N) input visits, after an O(P*N) first-seen search. It now
indexes input positions by package in one pass and visits each package group
once. First-seen package order and within-package input order are preserved.
Dependency digest aggregation now appends array elements directly instead of
using a concat temporary. The added focused fixture publishes two packages
in one SCC, loads each archive, and checks distinct package receipts.

A no-stub pure-Simple Stage 2 LLVM entry-closure build selected 69 modules,
completed parse and HIR, then failed MIR lowering before producing an
executable. The diagnostic set has 45 emitted errors (multiple passes of
the same sites): unsupported Result tuple payload extraction, unresolved
sorted/contains/concat methods, and non-array for-in lowering in
package_archive_cache, cas_batch_transaction, and interface_action_archive.
The concat site changed in this candidate to an array append loop; the
remaining sites were not modified. See the focused MIR bug. Log:
build/mini_builds/item6_archive_grouped_publish_native.log. A direct
Stage 2 CLI run attempt returned unknown command run; it did not execute
the fixture. No behavior, startup, RSS, or normalized-sum claim follows.

Next evidence: a current-source native compiler must build and run the
multi-package fixture, then a paired realistic SCC archive cohort must
measure p95 and peak RSS and apply the shared normalized-sum rule. Full
production Item 6 cutover and warm compiler cohorts remain open.
