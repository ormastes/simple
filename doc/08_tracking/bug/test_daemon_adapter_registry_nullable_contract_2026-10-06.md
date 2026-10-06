# Test daemon adapter registry nullable contract

Status: focused Phase1 verification passed. Pure-Simple native qualification remains pending; these results are not whole Phase1/current-candidate or release admission.

REQ-TDMN-REGISTRY-OPTIONAL traces the existing documented contract in `src/app/test_daemon/session_adapter.spl`: `find_for_meta` returns the adapter, or nil if none is found; `find_by_kind` implements the same missing-adapter branch. This repair introduces no new feature option. Matching lookups must preserve the selected adapter, and all8 broker callers already guard adapter.? before invoking methods.

The frozen Phase1 seed0f9/e590 collector ordinal16306 ran21examples;20failed with `nil is forbidden by the non-optional return contract of find_by_kind`. Both lookup methods explicitly returned nil but declared nonoptional SessionAdapter. The repair changes only those2 return annotations to SessionAdapter?. Selection loops, adapter values and broker production behavior are unchanged.

The new six-example unit spec covers empty and populated misses, exact kind/name selection, metadata selection and unsupported metadata. Actual bootstrap-Phase1 execution passed6/6,0skips, peak181780KiB. The repaired owner improved the existing system row to19/21. Its remaining2 stale assertions expected reusedcount1 despite existing broker initialization1/increment-on-reuse and an independent QemuBroker unit expectation2. Those2 examples now assert initialcount1, reusedcount2 and stable session identity; no production counter logic was changed. One changed previously-failed system-file cycle2 passed21/21,0skips, peak194088KiB. No unitPASS replay occurred.

Evidence owner: `/tmp/simple-test-daemon-nullable-evidence-20261006`.

- Original failure: `baseline/result.json` and `baseline/stdout.log` retain1passed/20failed.
- New unit: `unit/result.json`, `unit/rss.env` retain6passed/0failed/0skipped and quiescent1.
- First owner integration: `system/result.json` retains19passed/2failed; original stale assertions are preserved.
- Final changed system: `changed-system-cycle2/result.json`, `rss.env`, `invocation.env` retain21passed/0failed/0skipped, actual exit0 and quiescent1.
- Root kernel envelope: `/tmp/simple-test-daemon-nullable-counter-cycle2-kernel-20261006/kernel-containment-terminal.env` (root owns the actual envelope identity).

Candidate owner SHA256:a42584c2005784c4623d25d34f39049c9f97aa3fbbb17cb82c998bdb86cea728. Unit SHA256:908ec3b310bd16062f01bd79bfc4f6444a0c2f7614b272e6e41c6085ac33487d. Final system SHA256:8b790a45ecab8ee423f0291644eb7beabd937624dd750f2d707dc19e5b8a8ea3. Producer SHA256:0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7.

The exact seed lacks an example-name --filter option. The unsupported proposal was never launched and now fails closed. Its replacement ran only the changed previously-failed system file once. No frozen collector source, active compiler producer, runtime provider, or unrelated work was changed.

Canonical Phase1 docgen regenerated both manuals: 2 complete documents, 0 stubs, exit0, quiescent1, peak346008KiB. Manual review confirmed all6 unit and21 system executable scenario bodies and current reuse assertions. Seven existing system authoring warnings concern short documentation and missing overview/syntax/reference sections; they do not signify executable placeholders. Current generator omitted old redundant prose steps and an unrendered diagram placeholder while retaining every executable scenario. This is focused manual freshness evidence, not full documentation or release qualification.
