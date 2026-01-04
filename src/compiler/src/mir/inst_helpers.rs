// =============================================================================
// Helper methods for MIR instructions
// =============================================================================
//
// This section contains utility methods for querying instruction properties:
// - dest(): Get destination register
// - uses(): Get source registers
// - is_async(): Check if instruction is async
// - is_nogc(): Check if instruction doesn't allocate

impl MirInst {
    /// Check if this instruction is async (non-blocking).
    pub fn is_async(&self) -> bool {
        self.effect().is_async()
    }

    /// Check if this instruction is nogc.
    pub fn is_nogc(&self) -> bool {
        self.effect().is_nogc()
    }

    /// Destination register if this instruction defines one.
    pub fn dest(&self) -> Option<VReg> {
        match self {
            MirInst::ConstInt { dest, .. }
            | MirInst::ConstFloat { dest, .. }
            | MirInst::ConstBool { dest, .. }
            | MirInst::ConstString { dest, .. }
            | MirInst::ConstSymbol { dest, .. }
            | MirInst::Copy { dest, .. }
            | MirInst::BinOp { dest, .. }
            | MirInst::UnaryOp { dest, .. }
            | MirInst::Cast { dest, .. }
            | MirInst::Load { dest, .. }
            | MirInst::LocalAddr { dest, .. }
            | MirInst::GetElementPtr { dest, .. }
            | MirInst::GcAlloc { dest, .. }
            | MirInst::ArrayLit { dest, .. }
            | MirInst::TupleLit { dest, .. }
            | MirInst::VecLit { dest, .. }
            | MirInst::VecSum { dest, .. }
            | MirInst::VecProduct { dest, .. }
            | MirInst::VecMin { dest, .. }
            | MirInst::VecMax { dest, .. }
            | MirInst::VecAll { dest, .. }
            | MirInst::VecAny { dest, .. }
            | MirInst::VecExtract { dest, .. }
            | MirInst::VecWith { dest, .. }
            | MirInst::VecSqrt { dest, .. }
            | MirInst::VecAbs { dest, .. }
            | MirInst::VecFloor { dest, .. }
            | MirInst::VecCeil { dest, .. }
            | MirInst::VecRound { dest, .. }
            | MirInst::VecShuffle { dest, .. }
            | MirInst::VecBlend { dest, .. }
            | MirInst::VecSelect { dest, .. }
            | MirInst::VecLoad { dest, .. }
            | MirInst::VecGather { dest, .. }
            | MirInst::VecFma { dest, .. }
            | MirInst::VecRecip { dest, .. }
            | MirInst::VecMaskedLoad { dest, .. }
            | MirInst::VecMinVec { dest, .. }
            | MirInst::VecMaxVec { dest, .. }
            | MirInst::VecClamp { dest, .. }
            | MirInst::GpuAtomic { dest, .. }
            | MirInst::GpuAtomicCmpXchg { dest, .. }
            | MirInst::DictLit { dest, .. }
            | MirInst::IndexGet { dest, .. }
            | MirInst::SliceOp { dest, .. }
            | MirInst::Spread { dest, .. }
            | MirInst::FStringFormat { dest, .. }
            | MirInst::ClosureCreate { dest, .. }
            | MirInst::StructInit { dest, .. }
            | MirInst::FieldGet { dest, .. }
            | MirInst::PatternTest { dest, .. }
            | MirInst::PatternBind { dest, .. }
            | MirInst::EnumDiscriminant { dest, .. }
            | MirInst::EnumPayload { dest, .. }
            | MirInst::EnumUnit { dest, .. }
            | MirInst::EnumWith { dest, .. }
            | MirInst::UnionDiscriminant { dest, .. }
            | MirInst::UnionPayload { dest, .. }
            | MirInst::UnionWrap { dest, .. }
            | MirInst::FutureCreate { dest, .. }
            | MirInst::Await { dest, .. }
            | MirInst::ActorSpawn { dest, .. }
            | MirInst::ActorRecv { dest, .. }
            | MirInst::GeneratorCreate { dest, .. }
            | MirInst::GeneratorNext { dest, .. }
            | MirInst::TryUnwrap { dest, .. }
            | MirInst::OptionSome { dest, .. }
            | MirInst::OptionNone { dest, .. }
            | MirInst::ResultOk { dest, .. }
            | MirInst::ResultErr { dest, .. }
            | MirInst::InterpEval { dest, .. }
            | MirInst::ContractOldCapture { dest, .. }
            | MirInst::PointerNew { dest, .. }
            | MirInst::PointerRef { dest, .. }
            | MirInst::PointerDeref { dest, .. }
            | MirInst::GpuGlobalId { dest, .. }
            | MirInst::GpuLocalId { dest, .. }
            | MirInst::GpuGroupId { dest, .. }
            | MirInst::GpuGlobalSize { dest, .. }
            | MirInst::GpuLocalSize { dest, .. }
            | MirInst::GpuNumGroups { dest, .. }
            | MirInst::GpuSharedAlloc { dest, .. }
            | MirInst::NeighborLoad { dest, .. }
            | MirInst::ParMap { dest, .. }
            | MirInst::ParReduce { dest, .. }
            | MirInst::ParFilter { dest, .. }
            | MirInst::UnitWiden { dest, .. }
            | MirInst::UnitNarrow { dest, .. }
            | MirInst::UnitSaturate { dest, .. } => Some(*dest),
            MirInst::ParForEach { .. } => None,
            MirInst::Call { dest, .. }
            | MirInst::IndirectCall { dest, .. }
            | MirInst::Wait { dest, .. }
            | MirInst::InterpCall { dest, .. }
            | MirInst::MethodCallStatic { dest, .. }
            | MirInst::MethodCallVirtual { dest, .. }
            | MirInst::BuiltinMethod { dest, .. } => *dest,
            _ => None,
        }
    }

    /// Registers used by this instruction (excluding destination).
    pub fn uses(&self) -> Vec<VReg> {
        match self {
            MirInst::ConstInt { .. }
            | MirInst::ConstFloat { .. }
            | MirInst::ConstBool { .. }
            | MirInst::ConstString { .. }
            | MirInst::ConstSymbol { .. }
            | MirInst::GcAlloc { .. } => vec![],
            MirInst::Copy { src, .. } => vec![*src],
            MirInst::BinOp { left, right, .. } => vec![*left, *right],
            MirInst::UnaryOp { operand, .. } => vec![*operand],
            MirInst::Cast { source, .. } => vec![*source],
            MirInst::Load { addr, .. } => vec![*addr],
            MirInst::Store { addr, value, .. } => vec![*addr, *value],
            MirInst::LocalAddr { .. } => vec![],
            MirInst::GetElementPtr { base, index, .. } => vec![*base, *index],
            MirInst::Call { args, .. } => args.clone(),
            MirInst::IndirectCall { callee, args, .. } => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(*callee);
                v.extend(args.iter().copied());
                v
            }
            MirInst::Wait { target, .. } => vec![*target],
            MirInst::PatternTest { subject, .. } => vec![*subject],
            MirInst::PatternBind { subject, .. } => vec![*subject],
            MirInst::EnumDiscriminant { value, .. } => vec![*value],
            MirInst::EnumPayload { value, .. } => vec![*value],
            MirInst::EnumUnit { .. } => vec![],
            MirInst::EnumWith { payload, .. } => vec![*payload],
            MirInst::UnionDiscriminant { value, .. } => vec![*value],
            MirInst::UnionPayload { value, .. } => vec![*value],
            MirInst::UnionWrap { value, .. } => vec![*value],
            MirInst::FutureCreate { .. } => vec![],
            MirInst::Await { future, .. } => vec![*future],
            MirInst::ActorSpawn { .. } => vec![],
            MirInst::ActorSend { actor, message } => vec![*actor, *message],
            MirInst::ActorRecv { .. } => vec![],
            MirInst::GeneratorCreate { .. } => vec![],
            MirInst::Yield { value } => vec![*value],
            MirInst::GeneratorNext { generator, .. } => vec![*generator],
            MirInst::TryUnwrap {
                value, error_dest, ..
            } => vec![*value, *error_dest],
            MirInst::OptionSome { value, .. } => vec![*value],
            MirInst::OptionNone { .. } => vec![],
            MirInst::ResultOk { value, .. } => vec![*value],
            MirInst::ResultErr { value, .. } => vec![*value],
            MirInst::TupleLit { elements, .. }
            | MirInst::ArrayLit { elements, .. }
            | MirInst::VecLit { elements, .. } => elements.clone(),
            MirInst::VecSum { source, .. }
            | MirInst::VecProduct { source, .. }
            | MirInst::VecMin { source, .. }
            | MirInst::VecMax { source, .. }
            | MirInst::VecAll { source, .. }
            | MirInst::VecAny { source, .. }
            | MirInst::VecSqrt { source, .. }
            | MirInst::VecAbs { source, .. }
            | MirInst::VecFloor { source, .. }
            | MirInst::VecCeil { source, .. }
            | MirInst::VecRound { source, .. } => vec![*source],
            MirInst::VecExtract { vector, index, .. } => vec![*vector, *index],
            MirInst::VecWith {
                vector,
                index,
                value,
                ..
            } => vec![*vector, *index, *value],
            MirInst::VecShuffle {
                source, indices, ..
            } => vec![*source, *indices],
            MirInst::VecBlend {
                first,
                second,
                indices,
                ..
            } => vec![*first, *second, *indices],
            MirInst::VecSelect {
                mask,
                if_true,
                if_false,
                ..
            } => vec![*mask, *if_true, *if_false],
            MirInst::VecLoad { array, offset, .. } => vec![*array, *offset],
            MirInst::VecStore {
                source,
                array,
                offset,
            } => vec![*source, *array, *offset],
            MirInst::VecGather { array, indices, .. } => vec![*array, *indices],
            MirInst::VecScatter {
                source,
                array,
                indices,
            } => vec![*source, *array, *indices],
            MirInst::VecFma { a, b, c, .. } => vec![*a, *b, *c],
            MirInst::VecRecip { source, .. } => vec![*source],
            MirInst::VecMaskedLoad {
                array,
                offset,
                mask,
                default,
                ..
            } => vec![*array, *offset, *mask, *default],
            MirInst::VecMaskedStore {
                source,
                array,
                offset,
                mask,
            } => vec![*source, *array, *offset, *mask],
            MirInst::VecMinVec { a, b, .. } => vec![*a, *b],
            MirInst::VecMaxVec { a, b, .. } => vec![*a, *b],
            MirInst::VecClamp { source, lo, hi, .. } => vec![*source, *lo, *hi],
            MirInst::GpuAtomic { ptr, value, .. } => vec![*ptr, *value],
            MirInst::GpuAtomicCmpXchg {
                ptr,
                expected,
                desired,
                ..
            } => vec![*ptr, *expected, *desired],
            MirInst::DictLit { keys, values, .. } => {
                let mut v = Vec::with_capacity(keys.len() + values.len());
                v.extend(keys.iter().copied());
                v.extend(values.iter().copied());
                v
            }
            MirInst::IndexGet {
                collection, index, ..
            } => vec![*collection, *index],
            MirInst::IndexSet {
                collection,
                index,
                value,
            } => vec![*collection, *index, *value],
            MirInst::SliceOp {
                collection,
                start,
                end,
                step,
                ..
            } => {
                let mut v = vec![*collection];
                if let Some(s) = start {
                    v.push(*s);
                }
                if let Some(e) = end {
                    v.push(*e);
                }
                if let Some(s) = step {
                    v.push(*s);
                }
                v
            }
            MirInst::Spread { source, .. } => vec![*source],
            MirInst::StructInit { field_values, .. } => field_values.clone(),
            MirInst::FieldGet { object, .. } => vec![*object],
            MirInst::FieldSet { object, value, .. } => vec![*object, *value],
            MirInst::MethodCallStatic { receiver, args, .. }
            | MirInst::MethodCallVirtual { receiver, args, .. } => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(*receiver);
                v.extend(args.iter().copied());
                v
            }
            MirInst::BuiltinMethod { receiver, args, .. } => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(*receiver);
                v.extend(args.iter().copied());
                v
            }
            MirInst::FStringFormat { parts, .. } => {
                let mut v = Vec::new();
                for part in parts {
                    match part {
                        FStringPart::Literal(_) => {}
                        FStringPart::Expr(reg) => v.push(*reg),
                    }
                }
                v
            }
            MirInst::ClosureCreate { captures, .. } => captures.clone(),
            MirInst::InterpCall { args, .. } => args.clone(),
            MirInst::InterpEval { .. } => vec![],
            MirInst::ContractCheck { condition, .. } => vec![*condition],
            MirInst::ContractOldCapture { value, .. } => vec![*value],
            // Coverage probes
            MirInst::DecisionProbe { result, .. } => vec![*result],
            MirInst::ConditionProbe { result, .. } => vec![*result],
            MirInst::PathProbe { .. } => vec![], // No register uses
            MirInst::UnitBoundCheck { value, .. } => vec![*value],
            MirInst::UnitWiden { value, .. } => vec![*value],
            MirInst::UnitNarrow { value, .. } => vec![*value],
            MirInst::UnitSaturate { value, .. } => vec![*value],
            MirInst::PointerNew { value, .. } => vec![*value],
            MirInst::PointerRef { source, .. } => vec![*source],
            MirInst::PointerDeref { pointer, .. } => vec![*pointer],
            // GPU instructions
            MirInst::GpuGlobalId { .. }
            | MirInst::GpuLocalId { .. }
            | MirInst::GpuGroupId { .. }
            | MirInst::GpuGlobalSize { .. }
            | MirInst::GpuLocalSize { .. }
            | MirInst::GpuNumGroups { .. }
            | MirInst::GpuBarrier
            | MirInst::GpuMemFence { .. }
            | MirInst::GpuSharedAlloc { .. } => vec![],
            MirInst::NeighborLoad { array, .. } => vec![*array],
            // Parallel iterator instructions
            MirInst::ParMap { input, closure, .. } => vec![*input, *closure],
            MirInst::ParReduce {
                input,
                initial,
                closure,
                ..
            } => vec![*input, *initial, *closure],
            MirInst::ParFilter {
                input, predicate, ..
            } => vec![*input, *predicate],
            MirInst::ParForEach { input, closure, .. } => vec![*input, *closure],
        }
    }
}
