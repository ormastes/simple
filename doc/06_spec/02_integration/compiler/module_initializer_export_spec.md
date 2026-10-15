# Native module initializer export authority

Authored manual; generated docgen and SSpec execution are UNRUN pending an admitted pure compiled test host. This is not a generated PASS record.

| Requirement | Actual exercise | Required result |
| --- | --- | --- |
| REQ-MODULE-INIT-EXPORT-001 | Parse an initialized library global, lower and verify MIR, then emit actual LLVM IR for the nonentry module. | The generated initializer declares its canonical export and keeps that definition name; an ordinary library function remains qualified. |

Native acceptance additionally requires the repaired source-matched producer's planner to initialize its recorder globals and execute successfully. Existing Cranelift fixture success does not establish LLVM planner success. No seed interpreter fallback is authorized.

Final bounded evidence (2026-10-16): the small Cranelift storage/positive-recording fixture and LLVM planner startup passed. The larger native compiler-behavior probe completed HIR/monomorphization but stopped during MIR64/413 with semantic failures and RSS exit88; none of its assertions executed. This SSpec and generated docgen remain UNRUN. The supervisor and separate terminal assessment in `.simple/storage/build/phase3-mcdc-initializer-export-20261015/` preserve the distinction. These documentation updates postdate the frozen producer snapshots.
