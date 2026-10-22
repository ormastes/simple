# Native recursive MirType enum payload rejection

Status: source workaround proposed, native verification UNRUN; root cause unconfirmed.

The 9ad power fixture build reaches zero unresolved monomorphizations, then rejects six MirTypeKind construction payloads in production mir_types.spl: ScalableVec, Promise, Result, ActorType, Generator and Ptr. MIR completes 93/94 successfully. All six pass MirType values to enum payload declarations that also require MirType.

The proposed workaround names each concrete MirTypeKind in a typed local before constructing its outer MirType. It preserves all original payloads and validation. Source inspection does not prove contextual hint leakage: parameter HIR metadata and nominal alias comparison also participate, and the executing producer documents metadata ABI hazards. The workaround must pass an actual native rebuild and the production constructor fixture before being considered effective.

The same mir_types.spl blob passed MIR within an earlier 96-module registry fixture using Cranelift and low-memory streaming; the current power closure contains 94 modules and uses retained LLVM lowering. That different-input historical result does not validate the current candidate. No complete native executable or performance qualification follows from either MIR result.
