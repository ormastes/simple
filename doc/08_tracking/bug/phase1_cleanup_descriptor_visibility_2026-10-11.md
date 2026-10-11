# BUG-PHASE1-CLEANUP-DESCRIPTOR-VISIBILITY-20261011

Status: unresolved; three bounded cause cycles exhausted. No repair retained.

Release source: `95c12f073ffefa99ac774264beeedd68a47e7676`.
Actual owner: `src/compiler/99.loader/loader/exec_mapping_cleanup_v1.spl`.
Producer SHA256: `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
Qualification: BOOTSTRAP_ONLY_DIAGNOSTIC. No admitted native conclusion.

## Reproduction and observed cause

Earlier current-release recovery spec executed six cases, passing five and
failing canonical mapping identity after construction failure. The focused
`probe.spl` now inspects the real owner and the same mailbox cell before and
after its arm/publish/drain calls. `run.py` fixes the cached producer identity,
source closure, working directory, isolated cache and bounded timeout.

Caller-visible cell state:

| Point | Control handle | Control value | Token | Mapping ID |
| --- | --- | --- | --- | --- |
| Before arm | 1 | 0 | 0 | empty |
| After successful arm | 1 | 74 | 1 | empty |
| After failed publish | 1 | 74 | 1 | empty |

The arm method writes descriptor `mapping_id = canonical-map-id`, but this
ordinary text field is absent from the caller's stored cell. Its atomic token
and control values do propagate through shared native handles. Publisher then
refuses the descriptor and draining returns `native-outcome-empty`; no close
permit or release dispatch exists. The retained failure is therefore earlier
than the apparent missing close-permit mapping ID.

This proves the observable text-versus-handle split across the mailbox call
boundary. It does not yet distinguish cached interpreter argument cloning,
receiver writeback, or a production API requiring explicit returned state.
The exact class/parameter binder requires further owner analysis before a
production change is justified. The interpreter owner was consulted; its
existing array-parameter repair leaves method/self binding unchanged.

## Bounded receipts

| Cause cycle | Probe | Result |
| --- | --- | --- |
| 1 | Unmodified production owner | 0/1; arm true, publish false, drain empty |
| 2 | Direct array-element mutating receiver | same failure |
| 3 | Direct array-element text-field assignment | same failure |

Files: `baseline-identity-result.json`, `direct-receiver-result.json`,
`direct-field-result.json` and corresponding `.log` files. The exact executed
probe hash is `3dca46611abbbbfa38834979150cb620b3d16a80e904b01c7060cc5c56680c0c`.
The final experiment patch is retained in `direct-field-attempt.patch`; both
experimental source edits were restored and the worktree source diff is empty.
Restored owner SHA256:
`7693c5bafd4b77968589596c5937c1820d0fb28e13ee7de276ef547fe1c19dc1`.

No previously passing case was replayed, compiler rebuilt, cache deleted,
controller restarted, identity authentication removed, or dispatch fabricated.
The global candidate queue remains unchanged. Further investigation must use
new binder/ownership evidence or an admitted native comparison rather than
repeat these three experiments.

Next owner: interpreter/function and method-binding lane, coordinated with the
loader mailbox API owner. Trace the exact selected binder and class arena IDs
at function entry/exit before choosing a source repair. A native comparison
requires an admitted cached pure runtime; the closed hello preparation is not
authorization to rebuild or restart it. Existing production drafts 2993 and
2996 remain unqualified and unchanged.
