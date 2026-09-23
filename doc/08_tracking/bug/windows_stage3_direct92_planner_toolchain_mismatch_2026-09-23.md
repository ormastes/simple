# Windows Stage 3 direct diagnostic planner toolchain mismatch (2026-09-23)

Status: OPEN. Quarantined diagnostic stopped before a Stage 3 compiler invocation.

The exact92 admitted Stage 2 compiler passed the diagnostic's source, Git, runtime, and tool preflight. The isolated Windows `.exe` planner producer then failed to compile its main stub: GNU `gcc` rejected `--target=x86_64-w64-windows-gnu`. The producer emitted no planner receipt, so no Stage 3 candidate exists from this lane. Evidence: `D:/stage3-direct92-prep/lane.Dczw7q/planner-producer.log` and `D:/b-phase2-integrate/build/bootstrap92/admission/09f88830be44d93311feee9b4166aa54d072f7648870958274986957e5dd21f3/planner-build.log`.

This is planner toolchain selection, not proof that the coordinator handoff was fixed. The earlier exact8b canonical 12-thread coordinator still fails with `invalid-internal-argument:corrupt` before workers start; see `stage3_policy_handoff_native_corrupt_exact8b_2026-09-23.md`. A direct-route build, if later runnable, uses serial codegen and cannot qualify canonical 12-worker Stage 3 or authorize Phase 4. The session's third Stage 3 diagnostic cycle ended here; no retry was run.
