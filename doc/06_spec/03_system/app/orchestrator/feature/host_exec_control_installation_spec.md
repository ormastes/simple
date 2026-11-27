# Signed exec-control installation — authored specification

Status: **NOT_RUN / AWAITING_VERIFICATION**. Authored manual, not generated runtime evidence. No compiler, build, test or native provider execution ran. All local editing/static commands used shared CPU affinity 0–4.

Source: `test/03_system/app/orchestrator/feature/host_exec_control_installation_spec.spl` (thirteen cases).

| Requirement | Source prevention evidence |
| --- | --- |
| HOST-EXEC-CONTROL-INSTALL-01 | Real SDK dual Ed25519 proof verification; full canonical intent hash binds exact raw canonical control-policy object, enrollment digest, complete scope and baseline provider. Public standalone matcher rejects malformed shared envelope. Strict policy/wire quotas use UTF8 byte budgets. Bad signatures and stale root pins reject before mutation. |
| HOST-EXEC-CONTROL-INSTALL-02 | Actual SAME operation journal/archive/private-file publication; admit/begin precede config artifact, artifact readback precedes completed marker, marker precedes actual-scope reference. Actual filesystem artifact/index directory obstructions preserve latest owner/revision. Retry performs no duplicate begin or allocation, completed-index repair remains possible after old approval expiry. Different legitimately signed same-scope install is rejected even when index publication was interrupted. |
| HOST-EXEC-CONTROL-INSTALL-03 | Existing roots missing reference refuse loader. Changed proof cannot replace archive; wrong current scope does not adopt old reference. Outcome-unknown expired retry remains recovery-required. Exact expiry sampled after staging prevents final artifact publication. Public route malformed/oversized packet rejects before writer acquisition. No exec lease, readiness, provider command or extra resource debit is produced. |

Exact authored step trace (all NOT_RUN):

| Case | Exact `step()` text |
| --- | --- |
| 1 | installs exact signed bytes in the same journal with no extra resource debit or native command |
| 2 | rejects malformed shared envelopes and strict policy or wire violations |
| 3 | rejects actual signature corruption and stale root pins before journal mutation |
| 4 | retains executing publication failure and reconciles exact retry without another begin or debit |
| 5 | repairs completed missing index after old approval expiry and blocks second same-scope operation |
| 6 | keeps outcome-unknown retry marked recovery-required when its original proof has expired |
| 7 | never overwrites archived changed proofs or promotes installation across changed current scope |
| 8 | rejects malformed and oversized public route packets before opening a journal |
| 9 | rechecks exact expiry after stage IO before final policy publication |
| 10 | reopens completed installation as metadata while retaining original charge and quarantining old scope |
| 11 | refuses actual malformed packet and mismatched completed artifact on owned reopen |
| 12 | rejects actual orphan admitted installation row without its retained signed packet |
| 13 | reports actual new existing and conflicting private publication without issuing authority |

The fixture uses the real signature verifier, actual host operation WAL, generation-owned native journal lock and actual private filesystem writes. Only configured container/root observations are explicitly scripted fixture facts; this installer fixture executes no provider command. Its fresh owned journal authority is exactly host-<actual enrollment digest>, with one actual charged reservation and a separately tracked auxiliary fixture tree. Its `{fixtureOnly: true}` control object intentionally demonstrates schema opacity: installation does not claim it passes the actual common provider probe. The positive public CLI route on a real enrolled/native Linux root remains unexecuted; only its actual pre-open negative path is authored here.

Immutable files: original full request under journal `host-exec-control-installations/sha(op).sdn`; artifact under `host-exec-control-installation-artifacts/sha(op).sdn` is **exact canonical intent bytes**, whose hash is both original payload and completed outcome. Reference is `root/host-exec-control-installed-v3/<actual current scope fence>.sdn`; no caller path. Loader validates actual completed row, original packet, artifact and current enrollment/scope/provider/policy pins. Original signed installation request is retained in loaded data for the independently verified child delegation; producer must invoke loader rather than trust caller-created Installed values.

Missing runtime evidence: all thirteen cases, actual public successful CLI flow, native engines/common exec probe, native exec child/delegation producer, Windows ACL consumer, real process crash/power-loss boundaries, failed file fsync/consumed-close error, and genuinely ambiguous no-replace syscall outcome. No fake filesystem failure hooks or passing substitutes are used. Private stages are retained on ambiguous publication or uncertain readback/sync; orphan stages require explicit owner reconciliation, never blanket deletion. Same-scope expired unperformed config publication remains blocked; completed exact historical config may repair only its index without renewing old grants. New service epoch requires fresh explicit installation and its own immutable reference.

Historical projection uses a cycle-free read-only validator: actual exact journal envelope and signed packet, full intent matcher, trusted authority `host-<enrollment digest>` and same physical host. Completed metadata additionally requires the exact canonical intent artifact and matching outcome hash. Admitted/executing/unknown install rows allocate nothing and cannot activate config. Old boot/provider scope is structurally historical; forced quarantine may parse it but loader never promotes it. Actual owned reopen success/corrupt packet/corrupt artifact/orphan admitted row cases preserve or refuse real WAL history, without fake Released flags.

The shared publisher exposes context, published_new, recovery_required, error and exact retained stage_path. It restricts five exec domain directories, 64-lowercase-hex `.sdn` names and 1..4MiB bytes. Guard runs after stage/readback at the actual no-replace boundary. Actual new/existing/conflicting publication case verifies newness and preservation; neither file token nor newness alone is a live delegation. Child producer must require published_new plus empty error and independently committed/verified authority. All publication errors propagate exact stage location when retained; no blanket purge is authorized.
