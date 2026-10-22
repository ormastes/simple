# Module-static register array initializer inference fails

- Bug tag: `BUG-MODULE-STATIC-REGISTER-ARRAY-INFERENCE-20261011`
- GitHub: https://github.com/ormastes/simple/issues/3131
- Severity: P1; status: OPEN.
- Workaround: source-reviewed explicit type annotations; native verification UNRUN.

The actual direct-encoder probe used admitted producer SHA-256 `e6447d0d10f2c8ae552b67da8420a7e581a22bb55f79e4d4e4d30b981f095811` with a six-module whole-file projection from `26b790634335575981af5ccc8999082516e0c966`. HIR passed for all six modules. MIR then refused eleven module-static array initializers in `src/compiler/70.backend/backend/native/mach_inst.spl` with `cannot derive module static type from unresolved initializer; add an explicit annotation`. No production MIR serialization, Simple object or encoder executable was qualified. This was not a whole-compiler build. Assembler golden artifacts are separate and do not establish compiler success.

Retained evidence is `direct-encoder-manual-plan-26b790/attempt1/{error-groups.json,qualification.json,native-compile.stderr}` under the phase3-whole-20261011-c06 evidence root. The error set is exactly X86_ARG_REGS, X86_CALLEE_SAVED, X86_CALLER_SAVED, X86_ALLOCATABLE, X86_XMM_ALLOCATABLE, X86_YMM_ALLOCATABLE, AARCH64_ARG_REGS, AARCH64_CALLEE_SAVED, AARCH64_Q_ALLOCATABLE, RV_ARG_REGS and RV_CALLEE_SAVED.

The workaround adds `: [i64]` only to these eleven `val` declarations. Every referenced physical-register constant already has explicit scalar `i64` type. Values and initializer order, val mutability, names, callers and all other source bytes remain unchanged. Consumers use these values as register IDs through indexing, length, register arithmetic and allocator parameters explicitly typed `[i64]`. RV32 register IDs still use the existing i64 host representation; no target word width changes. No loop, allocation expression or execution path is added. Runtime/codegen/performance effects remain unmeasured.

Parent for this source child is `c9ebdcf673c0d5017c1e2577f891a6d2e34fee83`; its mach_inst bytes equal 26b7. Source SHA-256 before: `a7a0c305b1b50341e41ffb563d0a9e341119e0b6630d0506559a6a048c224991`; after: `3fb7d67a182c729568a0bbbdadd59e087f3d7c620c5e9872c3d1247a5af7270f`. Removing precisely the eleven annotations reproduces the full original file byte-for-byte.

This workaround does not repair compiler inference. The underlying pure-Simple compiler fix proceeds separately. Do not claim the annotations compile successfully until the same whole-file native fixture is run on the integrated child under a new root allocation. No new probe, compiler/test execution, cache cleanup, main edit or promotion is part of this source repair. Keep #3131 OPEN pending compiler repair and appropriate qualification.
