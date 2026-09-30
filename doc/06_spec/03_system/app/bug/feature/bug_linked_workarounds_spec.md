# Bug-linked workaround recovery manual

Status: authored manual; executable SPipe and generated evidence **TEST_BLOCKED**.
This file is not a generated passing test report.

Executable specification:
`test/03_system/app/bug/feature/bug_linked_workarounds_spec.spl`.
Filesystem transaction specification:
`test/02_integration/app/bug_workaround_store_spec.spl`.

1. Put `# @workaround bug=<canonical-id>` immediately above the affected source
   block. Add `recover=<7–64 hex Git reference>` and `reason=<text>` when useful.
   C-style `//` comments are accepted. IDs must exist in the canonical bug DB.
2. Run `simple check-dbs --fullscan bugs` to initialize the derived index.
   Ordinary parent native builds refresh changed/untracked and previously
   linked source paths in one locked transaction. Workers never publish it.
3. Run `simple check-dbs bugs --bug=<canonical-id>` to view source locations.
   This query reads the index and canonical bug DB without inspecting source.
4. Fix and verify the owning bug. A fixed/closed bug with remaining indexed
   workarounds produces a recovery-review warning. Compare the optional Git
   reference, restore only the affected intended code, and remove its marker.
5. Build the smallest affected scope to refresh removed links. Preserve unrelated
   edits and compatible caches. A missing or incomplete index requires fullscan;
   failed batches preserve previously valid bytes.

The executable scenarios assert marker diagnostics, source locations, quote
round trips, corruption rejection, deletion/reversion replacement, live bug
status joins, filtering, and incomplete-index visibility. The integration
fixture exercises real Git discovery and durable files. Runtime result counts,
generated captures, and latency measurements remain pending an admitted
general self-hosted runner. Compiler-only Stage 2 provenance does not establish
SPipe/docgen support.
