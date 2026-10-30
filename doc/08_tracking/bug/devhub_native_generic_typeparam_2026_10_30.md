# DevHub native closure reaches MIR with unsubstituted generic T

Status: OPEN. Owner: Codex root, 2026-10-30.

Full DevHub native build from release base `4efdcb2a7c1d209e77d1d1ea06b095b380c7096e` plus reviewed database callback/cleanup source failed under the explicitly supplied pinned Phase 2 producer (`13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`). Retained stderr records 43 TypeParam error occurrences across repeated captures, not necessarily43 distinct defects. The MIR summary reports two failed modules. The duplicate async HTTP encoder accounts for a separate unresolved to_string diagnostic and now has a focused native fix/pass.

Compiler guard owner in current source: `src/compiler/50.mir/_MirLowering/function_lowering.spl:1457`. It correctly rejects unresolved type parameters; do not replace T with i64/Any or suppress the error. The retained pinned compiler diagnostic omits the failing module and expression, so that location is not yet established. Periodic progress only brackets failures between module64 and128. An existing TLDR Future factory generic bug is related research, not proof of this cause.

Evidence: `build/devhub-release-dev-20261030/native-build.stderr.log`, frozen manifest and `build-observed-result.sdn`; tracked summary `doc/09_report/verification/devhub_native_build_20261030.md`. Build produced no executable; actual GUI launch remained NOT_RUN.

Unblock: identify the failing generic owner and instantiation using a supported scoped diagnostic on changed source, repair monomorphization or a proven library defect without erasing generic semantics, then build the complete DevHub entry and execute it. A focused encoder PASS cannot close this bug. No compiler rebuild or new producer admission is claimed.

Changed-source full-app run3 retained the generic failure after the HTTP encoder error disappeared:279/280 MIR modules succeeded, one failed,43 TypeParam occurrences, no executable. Receipt: `build/devhub-release-dev-20261030/full-app-run3/build-observed-result.sdn`. HIR reports unresolved mutex facade T imported by rt_hal/boundary; this is a lead only. Outer compiler exit0 conflicts with internal exit1 and absent output; never accept process exit alone. Finite app retry sequence stopped.
