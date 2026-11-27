# Shared scheduling work ownership

Status: research/design in progress; no source implementation or test PASS.

- Baseline compiler build: parent, frozen source in
  D:/dev/simple-phase2-test-runner-20261027; live handle 31772.
- Implementation source: work/phase2-runner-shared-scheduler-20261027,
  separate from the live baseline source and private caches.
- Small-model worker: read-only test-side research and proposed common-core
  implementation after parent resolves the interface/cursor design.
- Shared interfaces and manual step names: matching detail design document.
- Parent: common/build-side architecture, integration, final source/evidence/
  generated-manual review and PR landing. No sidecar finding is accepted
  without parent review; lower-model JSON-validator overclaim was corrected.
- Source adapters, focused specs and authored system manual now exist; execution
  and generated-manual review remain pending. Never count authored assertions
  or manual text as passing execution evidence.

Do not restart the live build or rerun existing green preflight checks. Retain
the authorized attempt's logs and use the resulting admitted GNU phase2
compiler only after real Hello compile/run qualification. Native runner and
full CLI evidence remain distinct gates.

## Bounded async evidence implementation update

Parent implemented unique per-child interpreter receipts through the internal
CLI --test-result-file flag, canonical structured result parsing and receipt
cleanup only after reaping. The parent environment is not changed. Native
child-test arguments/protocol remain unchanged. Small-worker review found no
P0/P1; its collision finding was fixed by refusing pre-existing receipt,
expectations or trace paths, and clearing ownership on admission refusal so
collection cannot delete someone else's receipt.

Added test/01_unit/lib/test_runner/async_structured_evidence_spec.spl with real
temporary-file assertions for green/red/missing/zero/deadline and reverse-order
collection. These are authored but UNRUN and prove no child transport by
construction; full parallel child and GNU Phase2 gates remain outstanding.
One scoped whitespace diff check passed before the final small ownership fix;
no compile/test success is claimed. No lockless map was added.
