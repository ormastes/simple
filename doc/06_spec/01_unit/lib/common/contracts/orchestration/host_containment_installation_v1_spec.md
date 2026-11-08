# Signed containment installation — authored specification

STATUS: NOT_RUN. This is an authored manual, not generated runtime evidence. No compiler, tests or builds were executed.

Source: `test/01_unit/lib/common/contracts/orchestration/host_containment_installation_v1_spec.spl`.

| Exact step | Status |
|---|---|
| roundtrips exact raw canonical policy and full opaque signed request bytes | NOT_RUN |
| validates standalone shared envelope shape and exact original operation correlation | NOT_RUN |
| rejects nonobject noncanonical wronghash unknown missing and oversized inputs | NOT_RUN |
| validates historical scope structurally without claiming current epoch or authentication | NOT_RUN |
| binds containment identity independently and refuses exec-control domain substitution | NOT_RUN |

HOST-CONTAINMENT-INSTALL-01 traces strict full-intent/domain/pin bytes; -02 traces signed same-WAL publication and conservative replay; -03 traces historical classification/current-root activation and domain separation. The unit cases treat signature bytes as opaque. System cases use real SDK signatures, owned operation journal and private IO with explicitly scripted trusted root/prior Container facts; they do not qualify native enrollment, containment observation, process teardown, Windows privacy, power-loss durability or effect enablement. Existing `host_exec_control_installation_spec.spl` remains the unchanged authored compatibility suite for the shared transaction. No positive readiness or contained-child teardown claim is made.
