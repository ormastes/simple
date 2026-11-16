# Restricted workspace source loan consumer

Status: **AUTHORED / NOT_RUN**. Handwritten companion to
`test/01_unit/lib/nogc_async_mut/container/providers/linux/workspace_source_loan_surface_v3_spec.spl`.

The capability leak was a raw SourceOwner returned to an external consumer:
its legacy close path can return original reader/storage/lease parents. The
upper producer now owns a separate restricted `LinuxWorkspaceSourceLoanV3`.
This consumer delta does not edit that helper, accepted Host V1, or Source FINAL6.

Four source regressions require only the approved V2 projection, program-match,
executable-profile and stage operations plus the genuine-capability factory;
no raw SourceOwner in Host V2 payload/return types; actual stage-returned loan
capture before readiness/error checks; and no raw source lifecycle/parent calls
from the Host V2 consumer. These enforce the exported source boundary and do
not claim runtime behavior or compiler privacy proof.

`test/fixtures/workspace_source_loan_v3/forbidden_access.spl` is deliberately
invalid compiler input. A qualified compiler must reject unavailable close and
private raw-owner/storage access. It has not been compiled; no diagnostic code
or successful rejection is fabricated. It is not an executable passing SSpec.

No positive test constructs a fake source, loan, descriptor or native lease.
Genuine stage behavior remains the accepted Source FINAL6 dependency. The loan
factory needs an already genuine source capability. Upper retains the original
source privately; Host retains each returned loan and the actual container,
without independently closing a borrowed view.

Runtime/compiler/native/SPipe execution remains **NOT_RUN**. Actual bounded
producer ports, observer/probe and retirement integration remain recorded in
the larger native consumer's unfinished dependency record. This delta claims
only the restricted consumer boundary and requires final combined review.
