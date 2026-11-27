# Signed containment installation — authored specification

STATUS: NOT_RUN. This is an authored manual, not generated runtime evidence. No compiler, tests or builds were executed.

Source: `test/03_system/app/orchestrator/feature/host_containment_installation_spec.spl`.

| Exact step | Status |
|---|---|
| installs exact signed bytes in the same journal with no extra resource debit or native command | NOT_RUN |
| rejects malformed shared envelopes and strict policy or wire violations | NOT_RUN |
| rejects actual signature corruption and stale root pins before journal mutation | NOT_RUN |
| retains executing publication failure and reconciles exact retry without another begin or debit | NOT_RUN |
| repairs completed missing index after old approval expiry and blocks second same-scope operation | NOT_RUN |
| keeps outcome-unknown retry marked recovery-required when its original proof has expired | NOT_RUN |
| never overwrites archived changed proofs or promotes installation across changed current scope | NOT_RUN |
| rejects malformed and oversized public route packets before opening a journal | NOT_RUN |
| rechecks exact expiry after stage IO before final policy publication | NOT_RUN |
| reopens completed installation as metadata while retaining original charge and quarantining old scope | NOT_RUN |
| refuses actual malformed packet and mismatched completed artifact on owned reopen | NOT_RUN |
| rejects actual orphan admitted installation row without its retained signed packet | NOT_RUN |
| reports actual new existing and conflicting private publication without issuing authority | NOT_RUN |
| keeps exec-control and containment completion references and signed domains disjoint | NOT_RUN |

HOST-CONTAINMENT-INSTALL-01 traces strict full-intent/domain/pin bytes; -02 traces signed same-WAL publication and conservative replay; -03 traces historical classification/current-root activation and domain separation. The unit cases treat signature bytes as opaque. System cases use real SDK signatures, owned operation journal and private IO with explicitly scripted trusted root/prior Container facts; they do not qualify native enrollment, containment observation, process teardown, Windows privacy, power-loss durability or effect enablement. Existing `host_exec_control_installation_spec.spl` remains the unchanged authored compatibility suite for the shared transaction. No positive readiness or contained-child teardown claim is made.
