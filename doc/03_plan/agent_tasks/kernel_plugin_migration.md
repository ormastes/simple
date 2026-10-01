<!-- codex-design -->
# Agent Tasks: Kernel/Plugin Migration

The primary contract pass freezes `IfaceId`, `ParamHeader`, `ParamExt`, all
manual `step("...")` strings, and all checker names from the matching SPipe
plan before sidecars start. The four user selections are recorded in
`doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`.

| Lane | Scope | Sidecar |
|---|---|---|
| Partition | closure classification and checker mutation fixtures | N/A until scheduled; concurrent dirty work exists |
| ABI/params | typed digest and parameter-object evolution | N/A until scheduled |
| Admission | ABI v1 and canonical `simple.sdn` negotiation | N/A; selected policy is fixed |
| Backends | LLVM-default plus Cranelift K1/P-static qualification | N/A; selected policy is fixed |
| Aspects | atomic APK-only coverage cutover | N/A; selected policy is fixed |
| Rebuild | P-edit/K0-edit cache and receipt proof | N/A until scheduled |
| Package ranges (Phase 8) | wire bounded caret/tilde `provides/requires` resolution into `simple lock`; retain resolution records; make unsatisfied ranges fail closed; add planned `test/01_unit/app/pkg/requires_range_spec.spl` evidence; do not add a backtracking solver | N/A until Phase 7 is complete; independent of KPM-OPT-1..4 selection |

**Merge owner:** compiler plugin-architecture integration owner.
**Final reviewer:** independent best-available normal/highest-capability reviewer
who did not implement a lane and rejects source-only or non-mutation evidence.
