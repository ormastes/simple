# HIR worker pre-surface path lookup allocations

Status: avoidable lookup allocation repaired; full-build memory cause remains open.

The retained Cranelift producer `e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6`
ran a bounded diagnostic with `SIMPLE_COMPILER_PHASE_PROFILE=1`, a 16 GiB
process-tree cap and a 300-second deadline. The parser reused all 3,024 cached
files. The HIR child reclaimed 3,024 source records (4,469 logical owners),
entered streaming phase 2 at 27.456 seconds, and emitted no surface-file marker
before the deadline. The overall run timed out (exit 143), peak 16,513,612 KiB.
Evidence: `/tmp/simple-phase2-phase-profile-diagnostic-attempt3-20261029.log`.

This narrows the unexplained growth to the pre-surface boundary; it does not
prove which operation owns it. Cache-scope publication, canonical-path
collection and worker import-closure planning precede the first surface marker.
Logical aliases account for the larger source-owner count; removing those
aliases would change import resolution.

The closure fallback lookup did concatenate `"/" + resolved` and `"/" + candidate`
for every inventory row of every unresolved canonical lookup. The repair uses
the equivalent suffix plus preceding-byte check, with no joined-path allocation.
Exact dictionary lookup and first matching inventory row retain their ordering.
Complexity remains O(import edges × inventory rows) for fallback scans. New
phase boundaries and coarse closure counters identify the remaining work on a
future rebuilt producer; this repair does not claim the whole memory issue fixed.

## Native differential evidence

The real native fixture `worker_surface_path_v1_probe.spl` compares the helper
against the old joined-path expression over 400 normalized path pairs, plus
three explicit component-boundary controls. It includes empty/root paths,
literal double separators, equality, Windows spellings and UTF-8 suffixes.
Its single execution returned exit 0 and `checks=403 failures=0`.

- Build/provenance: `/tmp/simple-hir-suffix-probe-20261029/inputs.sdn`;
  before/after target, runtime, producer and tool authority snapshots matched.
- Native artifact SHA256: `558bd767e354ef56a560dca55df57cb84424d8316a73ca3352e35f7630dd7bfe`.
- Build peak RSS: 2,821,576 KiB; Cranelift, retained producer above, 20 requested threads.
- Guide and Astra independently reviewed the implementation with no P0/P1/P2 findings.

This is scoped native helper evidence, not rebuilt compiler, SSpec execution,
MCP/core smoke, bootstrap qualification or measured full-closure RSS improvement.
