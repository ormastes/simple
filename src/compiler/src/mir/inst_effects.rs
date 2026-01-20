// =============================================================================
// HasEffects trait implementation for MIR instructions
// =============================================================================
//
// This section contains the effect tracking logic for all MIR instructions,
// enabling compile-time verification of async/nogc properties.

impl HasEffects for MirInst {
    /// Return the effect of this instruction.
    /// Enables compile-time verification of async/nogc properties.
    fn effect(&self) -> Effect {
        match self {
            // Pure computation
            MirInst::ConstInt { .. }
            | MirInst::ConstFloat { .. }
            | MirInst::ConstBool { .. }
            | MirInst::ConstString { .. }
            | MirInst::ConstSymbol { .. }
            | MirInst::Copy { .. }
            | MirInst::BinOp { .. }
            | MirInst::UnaryOp { .. }
            | MirInst::Cast { .. }
            | MirInst::Load { .. }
            | MirInst::Store { .. }
            | MirInst::LocalAddr { .. }
            | MirInst::GetElementPtr { .. }
            | MirInst::IndexGet { .. }
            | MirInst::IndexSet { .. }
            | MirInst::SliceOp { .. }
            | MirInst::FieldGet { .. }
            | MirInst::FieldSet { .. }
            | MirInst::EnumDiscriminant { .. }
            | MirInst::EnumPayload { .. }
            | MirInst::UnionDiscriminant { .. }
            | MirInst::UnionPayload { .. }
            | MirInst::PatternTest { .. }
            | MirInst::PatternBind { .. }
            | MirInst::ContractOldCapture { .. }
            | MirInst::PointerDeref { .. }
            | MirInst::VecSum { .. }
            | MirInst::VecProduct { .. }
            | MirInst::VecMin { .. }
            | MirInst::VecMax { .. }
            | MirInst::VecAll { .. }
            | MirInst::VecAny { .. }
            | MirInst::VecExtract { .. }
            | MirInst::VecWith { .. }
            | MirInst::VecSqrt { .. }
            | MirInst::VecAbs { .. }
            | MirInst::VecFloor { .. }
            | MirInst::VecCeil { .. }
            | MirInst::VecRound { .. }
            | MirInst::VecShuffle { .. }
            | MirInst::VecBlend { .. }
            | MirInst::VecSelect { .. }
            | MirInst::VecLoad { .. }
            | MirInst::VecGather { .. }
            | MirInst::VecFma { .. }
            | MirInst::VecRecip { .. }
            | MirInst::VecMaskedLoad { .. }
            | MirInst::VecMinVec { .. }
            | MirInst::VecMaxVec { .. }
            | MirInst::VecClamp { .. } => Effect::Compute,

            // SIMD store/scatter have memory write effects
            MirInst::VecStore { .. }
            | MirInst::VecScatter { .. }
            | MirInst::VecMaskedStore { .. } => Effect::Io,

            // Contract checks may panic (Io effect due to potential panic)
            MirInst::ContractCheck { .. } => Effect::Io,

            // Coverage probes (Io effect since they write to coverage collector)
            MirInst::DecisionProbe { .. }
            | MirInst::ConditionProbe { .. }
            | MirInst::PathProbe { .. } => Effect::Io,

            // Unit bound checks may panic in debug mode (Io effect due to potential panic)
            MirInst::UnitBoundCheck { .. } => Effect::Io,

            // Unit conversions (widen is compute, narrow may panic, saturate is compute)
            MirInst::UnitWiden { .. } => Effect::Compute,
            MirInst::UnitNarrow { .. } => Effect::Io, // May panic on overflow
            MirInst::UnitSaturate { .. } => Effect::Compute, // Clamping is pure compute

            // Collection allocation (GcAlloc effect)
            MirInst::ArrayLit { .. }
            | MirInst::TupleLit { .. }
            | MirInst::VecLit { .. }
            | MirInst::DictLit { .. }
            | MirInst::Spread { .. }
            | MirInst::FStringFormat { .. }
            | MirInst::ClosureCreate { .. }
            | MirInst::StructInit { .. }
            | MirInst::EnumUnit { .. }
            | MirInst::EnumWith { .. }
            | MirInst::UnionWrap { .. }
            | MirInst::OptionSome { .. }
            | MirInst::OptionNone { .. }
            | MirInst::ResultOk { .. }
            | MirInst::ResultErr { .. }
            | MirInst::FutureCreate { .. }
            | MirInst::GeneratorCreate { .. }
            | MirInst::PointerNew { .. }
            | MirInst::PointerRef { .. } => Effect::GcAlloc,

            // Function calls - effect depends on target
            MirInst::Call { target, .. } => target.effect(),

            // Indirect call - uses provided effect annotation
            MirInst::IndirectCall { effect, .. } => *effect,

            // Method calls may have side effects
            MirInst::MethodCallStatic { .. }
            | MirInst::MethodCallVirtual { .. }
            | MirInst::BuiltinMethod { .. } => Effect::Io,

            // Explicit effect markers for verification
            MirInst::GcAlloc { .. } => Effect::GcAlloc,
            MirInst::Wait { .. } => Effect::Wait,

            // Blocking operations
            MirInst::Await { .. }
            | MirInst::ActorRecv { .. }
            | MirInst::ActorJoin { .. }
            | MirInst::GeneratorNext { .. }
            | MirInst::TryUnwrap { .. } => Effect::Wait,

            // Non-blocking I/O
            MirInst::ActorSpawn { .. }
            | MirInst::ActorSend { .. }
            | MirInst::ActorReply { .. }
            | MirInst::Yield { .. } => Effect::Io,

            // Interpreter fallback (temporary - will be removed)
            MirInst::InterpCall { .. } | MirInst::InterpEval { .. } => Effect::Io,

            // GPU instructions - pure compute on GPU (no GC, synchronous from kernel perspective)
            MirInst::GpuGlobalId { .. }
            | MirInst::GpuLocalId { .. }
            | MirInst::GpuGroupId { .. }
            | MirInst::GpuGlobalSize { .. }
            | MirInst::GpuLocalSize { .. }
            | MirInst::GpuNumGroups { .. }
            | MirInst::GpuMemFence { .. }
            | MirInst::NeighborLoad { .. } => Effect::Compute,

            // GPU barrier is a synchronization point (Wait effect)
            MirInst::GpuBarrier => Effect::Wait,

            // GPU atomics and shared memory allocation
            MirInst::GpuAtomic { .. } | MirInst::GpuAtomicCmpXchg { .. } => Effect::Io,
            MirInst::GpuSharedAlloc { .. } => Effect::Compute,

            // Parallel iterator operations - all have Compute effect (parallel execution)
            MirInst::ParMap { .. }
            | MirInst::ParReduce { .. }
            | MirInst::ParFilter { .. }
            | MirInst::ParForEach { .. } => Effect::Compute,

            // Memory safety instructions
            // Drop may call destructors which could have I/O effects
            MirInst::Drop { .. } => Effect::Io,
            // EndScope is a no-op marker for lifetime analysis
            MirInst::EndScope { .. } => Effect::Compute,
        }
    }
}
