# Release Phase3 persistent-root promotion port — 2026-10-25

Status: focused runtime repair; original Stage3 workload remains unqualified.

## Provenance and boundary

Audit base: `005197db5713d236c52ea26c277db1cb077b89dd`, confirmed against remote
`release_phase3` before creating the isolated worktree. Before publication the
patch was rebased without conflicts onto `75d260930c3`; runtime code and tests
were unchanged by that rebase. Donor:
`5bd66c7d3f518a707c725f4ade039b6ebf17a7a1` from the separate
`/tmp/release-1.0.0-phase3-fixes` repository. Its runtime patch applies cleanly;
the target promotion prefix matches the donor beforeimage, and the complete
repaired promotion function matches the donor afterimage. Production changes
are limited to that existing shortcut correction. No compiler query, source
syntax, cache wire format or promotion-root list changes are included.

The preserved crash belongs to producer SHA-256
`7934d8c2e119a56098c49c0d996c52070eb962e156ce3855a723d29824cbf550`,
source `1690b09c34dd45df444d95bb02eeda568dd9f0b0`. At diagnosis its matching
report was `/var/crash/_tmp_phase3-stage3fix-1690_canonical-admission_stage2_aarch64-unknown-linux-gnu_simple.1000.crash`.
Saved stack, array-state and static-disassembly evidence remains in
`/tmp/phase3-stage3-1690-core-review/`. The cleanup owner subsequently removed
only the expanded 4.2 GiB CoreDump after matching its stream hash to the then
readable report. Apport later reused that report pathname; the current report
is partial/different, so complete recovery of the original core is uncertain.
Do not treat that mutable pathname as the original immutable evidence. The
recorded diagnosis and source review depend on the preserved readouts, not on
a future core reconstruction. No replay, debugger injection or live-memory
mutation was used.

`stack.log` places SIGSEGV at `surface_decl_owner_indices+664` (`0x88f818`),
through imported callable dependency materialization while lowering
`compiler.driver.driver`, after one successful HIR module. The faulting
string-array slot read has an invalid saved array header/data pointer.
This locates the failure; the core alone does not establish when the carrier
became invalid. The 6,393,228 KiB peak process-tree RSS stayed below the
8,388,608 KiB guard; the recorded terminal result is signal 11, not OOM.

Static disassembly of this exact producer confirms the old runtime shortcut:
any registered heap root outside the active scope returns success before child
traversal. `lower_retained_surface_module` pauses the scope before calling
`promote_phase_memo_transient_owners`, which constructs its wrapper array after
the pause. Persistent mutable roots can therefore hide transient children.
All four index arrays are already named in the compiler's promotion root list.
The existing donor fixes this runtime defect by allowing only immutable
String/Float/Int/UInt leaves to take the shortcut. Containers use the existing
bounded traversal and commit path; the C runtime counterpart already traverses
persistent containers. A repaired compiler run is still needed to establish
whether this explains and repairs the original Stage3 crash.

## Focused validation

Evidence directory: `/tmp/phase3-persistent-root-evidence-20261025/`.
Private Cargo target: `/tmp/phase3-persistent-root-cargo-20261025/`; dependency
artifacts were copied from the retained donor test cache, and path/source
changes were rebuilt by Cargo. Toolchain: rustc 1.99.1 / cargo 1.99.1.
Commands use `--offline --locked`, two build jobs and finite timeouts.

- `fixed-tests2.log`: 22 ownership/string tests PASS, zero failed. Covers the
  donor persistent array/new-child and paused diagnostic-root regressions,
  persistent dictionary cycles with new children across scopes, scope abort
  without successful promotion, existing array/tuple/packed-array/alias graph
  and share-window controls, plus bounded growth. Runtime test duration 0.01 s.
- The initial compile failed on a missing qualification in a new test call;
  `fixed-tests.log` preserves that result. No production change was needed.
- `negative-tests.log`: restoring only the old shortcut makes the donor paused
  diagnostic-root regression FAIL: managed message length -1 versus expected
  59. This assertion occurs before raw record dereference. The fixed source was
  restored byte-for-byte after that process exited; no build used moving source.
- `fixed-unit-test-binary` preserves the passing suite artifact separately from
  subsequent negative-control compilation. Artifact hashes and source identity
  are recorded in the local SDN evidence manifest.

## Performance limits

The correctness fix is not claimed performance-neutral. Without a write
barrier, a persistent mutable graph must be revisited because it may contain
new transient children. One promotion traverses the reachable graph and filters
the current scope's object list. For R rounds appending B children to one root,
full-graph rewalk contributes B*R*(R+1)/2 array slots cumulatively: quadratic in
R at fixed B, although an individual traversal remains graph-sized.

The small measurement in `fixed-tests2.log` records 8/16/32 rounds with 32 new
children each: 1,152/4,352/16,896 expected rewalk slots and
85,023/287,311/1,064,813 ns in promotion. Expected slot counts derive from the
fixture shape; they are not instrumented internal visit counts. These short
single samples are diagnostic evidence, not a benchmark threshold or a claim
about the original compiler workload. Cargo's peak RSS includes compilation
and must not be reported as runtime RSS.

A separately invoked ignored measurement case exercises 64/128/256 rounds with
64 children per round and checks every retained child's length before freeing
it. It is separate from the always-run correctness tests and has no fabricated
performance threshold. Its direct executable invocation provides runtime RSS. `benchmark-runtime.log`
records PASS for that distinct measurement case, with the following single-run
samples:

| Rounds | Final children | Expected cumulative rewalk slots | Promotion time |
|---:|---:|---:|---:|
| 64 | 4,096 | 133,120 | 9.34 ms |
| 128 | 8,192 | 528,384 | 34.11 ms |
| 256 | 16,384 | 2,105,344 | 127.63 ms |

The whole direct benchmark process took 0.18 s and peaked at 7,072 KiB RSS
(`/usr/bin/time -v`, `benchmark-runtime.time`); this excludes Cargo compilation.
Increasing rewalk cost is visible, not hidden as a performance-neutral repair.
The measurement neither models the full compiler graph nor establishes a
production memory bound. No passing functional case was rerun for measurement.

## Remaining admission work

No new production runtime authority or compiler has been admitted. Unit-test
executables are diagnostic artifacts only. Rebuild the appropriate immutable
runtime authority with fresh source/tool/artifact hashes; never retain the old
runtime identity for changed bytes. Then relink/rebuild a source-consistent
producer and run the original driver graph through the early HIR boundary,
with bounded elapsed time and RSS. Preserve any independent failure. No full
bootstrap, full Phase3 PASS, original-workload repair, or speedup is claimed.
