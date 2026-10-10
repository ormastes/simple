# CUDA unary MIR type OR alternatives lose enum ownership

Status: OPEN; tagged source workaround, not a compiler repair. Native verification pending.

Actual b9 Phase3: 1159/1160 HIR modules passed; CUDA failed seven unique binding-mismatch diagnostics `[I16]` versus I32/I64/U16/U32/U64/F32/F64. Receipt: /mnt/c/Temp/simple-phase3-tagged-b9-terminal-evidence-20261010/failed-file-manifest.json. Producer aa404c21c4d2435e871ac0f57903da18610b452323fe09355f86b9cdddb0a41f, source b9ccb2ab9c86017724f29e5a2985dfe9b25d60dd.

Owner proof: cuda_backend.spl operand_mir_type returns Result<MirType, CompileError> (1411); UnaryOp unwraps it at351 and matches dest_mir_ty.kind at357/365. mir_types.spl145–150 declares MirType.kind: MirTypeKind, with these unit alternatives. Qualify precisely the two unary alternatives; preserve all bodies, guards, diagnostics, other OR payload bindings, and static CUDA registration. This does not exclude CUDA or change static/dynamic/off selection.

Primary reproducer: native-build actual src/plugins/backend_cuda/cuda_backend.spl using the recorded producer and normal dependency closure. No fourth full-scope HIR retry is authorized. A successful targeted compile must prove the CUDA module HIR artifact and still report dependency failures separately. It cannot invent an aggregate1160 PASS stamp.

Nearby fixture test/fixtures/compiler/cuda_unary_type_owner_probe/main.spl checks negation integer/float inclusion, Boolean/I8 exclusion, bit-not integer inclusion and float exclusion. UNEXECUTED; expected stdout 1/1/0/0/1/0 on separate lines. It is a control, not a substitute for the actual CUDA reproducer. SPipe/core checks and dynamic CUDA artifact qualification remain pending.

Workaround source commit: b7402e324 (parent b9ccb2ab9c86017724f29e5a2985dfe9b25d60dd). This follow-up registers the OPEN primary and active BUGDB rows and canonical @workaround tags. Qualifying evidence and release PR linkage must be appended after actual execution; no PASS is inferred from source review.
