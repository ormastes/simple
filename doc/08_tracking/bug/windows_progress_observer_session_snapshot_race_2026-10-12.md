# Session job membership races with native process snapshots

The Windows progress observer takes a Win32_Process snapshot and then queries
each reachable bootstrap supervisor's named Job Object. These APIs do not form
an atomic snapshot. A process can start or exit between them. Previously any job
member absent from the earlier process snapshot rejected the entire sample.
Additionally, the first job query lazily initialized its C# interop with
Add-Type, which can spawn csc after the process snapshot and create this race
inside the observed job itself.

The live phase3 attempt3 observer failed for supervisor 16432 with absent job
members while compiler.snapshot processes 5160 and 21080 remained active. A
read-only native comparison retained under
`C:/dev/simple-phase3-hir-memory-evidence/observer-race/` reproduced the frozen
observer's exit 1 for missing member 16432/20824 with zero rows. The repaired
observer returned exit 0 and 27 rows, including both compiler processes with
1897024 and 3839432 KiB RSS at that later sample. This is observer correctness
evidence, not compiler qualification or a workload memory comparison.

The repair initializes interop before taking the first process snapshot. Only
the precise missing-member race authorizes a retry, bounded to three complete
fresh process snapshots and authoritative job queries. A newly started member
must appear with valid metrics and birth identity; a retired member must no
longer appear in the fresh authoritative membership query. Get-Process absence
is not used as retirement proof. Persistent absent/unknown/live owned members,
job query failures and invalid required metrics still reject the whole result.
The converter publishes no partial process tree, and the observer never kills,
reparents or controls a workload process.

`scripts/check/check-windows-process-observer.ps1` passed 31 executed assertions
on native Windows PowerShell. Added cases exercise initialization ordering,
members born after a snapshot, membership retirement before a refreshed query,
three-attempt exhaustion with zero published rows, and immediate rejection of
non-race ownership/metric failures. No Simple compiler job or test fallback was
used. Frozen campaign source and running jobs were left untouched.
