# Genuine Controller canonical-custody regression

Status: **AUTHORED_NOT_RUN**. Routing source cycle **5/6**. No native, test,
compiler, build or seed execution occurred. This is a mandatory actual fixture,
not mocked capabilities or a source-only substitute for native evidence.

Executable source:
`test/03_system/app/orchestrator/feature/controller_dispatch_canonical_custody_v3_spec.spl`.

The qualification machine must provide
`C:\SimpleQualification\controller-custody-v3.sdn` with exactly three public
text fields: `controllerRoot`, `controllerConfigDigest`,
`expectedEnrollmentDigest`. The first two must identify an already installed,
dedicated real local Windows Controller root with its actual pinned V3 config,
protected setup reader and a live authenticated Host. The enrollment digest is
independently recorded from that genuine Host deployment. No secrets, root
handles, reader objects, exchange proofs or raw capability DTOs are loaded.

The test acquires actual custody through `controller_local_root_open_v3` and
`controller_dispatch_service_begin_v3(root,"service-stop")`. It saves handle A
during real E1 status, then repeats begin with the SAME actual input Root copy.
That duplicate must refuse with the existing current handle and no bare root
cleanup carrier, phase change or new exchange. The fixture deliberately adopts
the returned current handle; the refusal must not poison canonical operation.
It then polls
by observed production DATA phase
with an actual monotonic deadline until E1's verified proof is consumed and E2
is begun. It does not assume a phase after any fixed number of steps.
Status loops also have a 512-step maximum; local drain has a 256-step maximum.
All use 5ms SOSIX sleep, preventing unbounded busy polling without imposing a
1.28s status budget below the existing 2s exchange timeout. No performance result is claimed.

At `phase=service-stop`, the SAME uninterrupted status-consumption call has
created E2. The lower exchange **begin** connects and queues hello bytes; only
a subsequent lower exchange **step** writes bytes. No E2 step is performed
before this test closes it. Therefore no authenticated stop request is sent.
This source call-path fact must be rechecked if the lower exchange begin API
changes; a fixture must never guess that a stop was harmless.

Calling close(A) must return explicit stale refusal with latest E2 handle and
unchanged canonical phase/outcome. It must not close any E2 socket, reader or
Controller root. The test deliberately adopts the returned latest handle,
then closes E2 through the canonical path. Cancellation remains nonzero and
Unknown; local completion never proves remote service-stop occurred.

Next, the test reopens the real Controller root and starts authenticated status,
reusing a retired slot. The old E2 identity must now refuse as retired without
returning any handle to the new operation. The new actual status must succeed
with ready=true and the independently expected enrollment digest, proving the
Host remains live after the unsent E2 was drained.

Whole actual root/turn carriers are retained globally before assertions, including
failure. Duplicate/stale/retired returned turns have a SEPARATE retained slot
until refusal and exact current-handle DATA equality are verified; original B
remains retained too. Only then is the returned current handle deliberately
adopted. Local cleanup always consumes returned handles. Retention is only
in this process; it does not serialize native ownership past process exit.
Missing fixture, origin refusal or resource failure is a failure, never skip/pass.

Further genuine scenarios remain **NOT_RUN** procedures, not fabricated tests:

1. Under an actual currently signed workload fixture, save A during E1 status;
   reach E2 validate, then E3 prepare. Old closes must refuse at both transitions,
   and deliberately adopted canonical continuation must retain the live current
   socket before its reader/root. Record actual setup and provider receipts.
2. While canonical state is busy, originate a permitted same-thread reentrant
   call through a genuine native test harness. It must refuse without inspecting
   or mutating in-flight custody. Do not fake thread IDs or bypass origin checks.
3. Copy an actual Controller root before and after real assignment WAL advance;
   repeated begin must refuse with the existing current handle and no duplicate
   root cleanup carrier or second exchange. A stale root's failed current-WAL
   metadata check must not cause it to escape as independently closable cleanup.
4. Exercise actual origin failure before registration and capacity refusal with
   genuine distinct admitted roots. The original supplied root must remain in
   a private cleanup-only unregistered arm without any unguarded registry
   allocation or bare root_cleanup escape. On permitted-origin cleanup, compare
   all active native Root identities first. A duplicate returns current handle;
   indeterminate retains the arm; only definite no-match may close the Root.
   Inject an actual consumed-unconfirmed Root close through an admitted native
   failure harness: owner=nil must not become completed=true, no native retry
   occurs, and the original registration refusal plus late close error/disposition
   remain recorded. No fake Root or native carrier may stand in for this case.
5. The ceiling decision has pure assertions; no test mutates a private live
   registry or fabricates a near-ceiling native owner. Any native qualification
   must use legitimate repeated generations or an independently reviewed native
   fault-injection surface, which this change does not add.
