# Original workspace preparation deadline

Status: AUTHORED_NOT_RUN. Production helper: `container_workspace_preparation_deadline_v3`, called by the actual original-source context producer. Spec: `test/01_unit/lib/container/workspace_preparation_window_v3_spec.spl`.

| Case | Expected production DATA result |
|---|---|
| Original 1000ns, budget2ms, later samples | Same fixed deadline2001000ns |
| Exact deadline or a later step | Original preparation expired |
| Clock rollback, zero wall sample or signed wall expiry | Refusal |
| Overflow, zero or unsupported budget | Refusal before addition |

These are arithmetic/source regressions, not fabricated native clocks, protected invocation grants, process owners or kernel fault coverage. Genuine source/cleanup fixture lives in the separately authored startup fixture snapshot; numeric WAL/quota sampling and consumed-close native fault injection are NOT_COVERED. No compiler/test/native execution was authorized. Complete provider probes, interactive transport and retained-workspace finalization remain outside this partial checkpoint.

Consolidated continuation P1 regression additions (all AUTHORED_NOT_RUN): the real final-admission arithmetic rejects a delay crossing the original deadline between planning and spawn; shorter FullV2 wall expiry caps native expiry; before/after monotonic brackets preserve the fixed original ceiling; reversed/expired/overflow samples refuse. These are used by the actual post-WAL effect gate, not a test-only mirror.

Delayed Start final-delivery kernel scenario remains NOT_COVERED without a qualified full workspace fixture whose approved payload exits between association publication and the next reply step. The production correction reobserves actual retained native subject via running_v2 and refuses Empty/unknown. No copied DTO, caller PID, fake EmptySnapshot or synthetic native close fault is substituted as test evidence. Startup-only genuine source fixture cannot establish this running-payload race.

Final round6 Attach boundary cases (AUTHORED_NOT_RUN): initial admitted1050ms; later original monotonic deadline crossed while wall1040ms remains before both helper1050 and signed5000 => refusal. With monotonic9ms remaining, production cap becomes1048 rather than prepared1050; actual Attach refuses the mismatch to preserve existing Session/helper correlation. An already prepared1045ms expiry remains unchanged under the same samples. Native WAL-delay injection and actual transport launch counts are NOT_COVERED; these tests establish the production arithmetic decision only.
