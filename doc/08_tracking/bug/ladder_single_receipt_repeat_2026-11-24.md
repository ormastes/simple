# Single downloaded receipt did not block an unchanged failed seed

Run 45211128098 Windows rung 2, job 137849961881, downloaded the rung 1
receipt artifact 14840107033 successfully at 16:45:26 UTC on November 23.
The action matched one artifact and extracted directly into
build/ladder/diagnostics. The guard scanned only one child directory below
that root, so it missed seed-native-failure.sdn despite matching source
68bb1b5d22340f9f730d37e584033793a821f0ce, windows-x86_64 and four threads.
It cold-built the same seed closure and repeated all thirteen timestamp and
progress duplicate symbols at 17:22:49 UTC. This is separate from the runtime
provider collision repair.

The guard now inspects both the flat single-artifact layout and the nested
multiple-artifact layout. It still requires all three identity fields and
does not admit a retained cache or treat a failed compiler as a handoff.

The regression executes the actual shell guard. Before repair, the flat
matching case returned 0 instead of 86. After repair, both matching layouts
refuse continuation; changed source, platform or thread count and absent
receipts continue. These are orchestration tests, not compiler qualification.
