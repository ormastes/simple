// =============================================================================
// MIR instruction enum definition
// =============================================================================
//
// This section contains the main MirInst enum with all 80+ instruction variants.

/// MIR instruction
#[derive(Debug, Clone, PartialEq)]
pub enum MirInst {
    /// Load constant integer
    ConstInt { dest: VReg, value: i64 },

    /// Load constant float
    ConstFloat { dest: VReg, value: f64 },

    /// Load constant bool
    ConstBool { dest: VReg, value: bool },

    /// Copy value from one register to another
    Copy { dest: VReg, src: VReg },

    /// Binary operation
    BinOp {
        dest: VReg,
        op: BinOp,
        left: VReg,
        right: VReg,
    },

    /// Unary operation
    UnaryOp {
        dest: VReg,
        op: UnaryOp,
        operand: VReg,
    },

    /// Type cast operation
    Cast {
        dest: VReg,
        source: VReg,
        from_ty: TypeId,
        to_ty: TypeId,
    },

    /// Function call with effect tracking
    Call {
        dest: Option<VReg>,
        target: CallTarget,
        args: Vec<VReg>,
    },

    /// Load from memory
    Load { dest: VReg, addr: VReg, ty: TypeId },

    /// Store to memory
    Store { addr: VReg, value: VReg, ty: TypeId },

    /// Get address of local variable
    LocalAddr { dest: VReg, local_index: usize },

    /// Get element pointer (for arrays/structs)
    GetElementPtr { dest: VReg, base: VReg, index: VReg },

    /// GC allocation (explicit for verification)
    GcAlloc { dest: VReg, ty: TypeId },

    /// Blocking wait (explicit for verification)
    Wait { dest: Option<VReg>, target: VReg },

    // =========================================================================
    // Pointer instructions
    // =========================================================================
    /// Allocate a new pointer wrapping a value
    PointerNew {
        dest: VReg,
        kind: PointerKind,
        value: VReg,
    },

    /// Create a borrow reference (immutable or mutable)
    PointerRef {
        dest: VReg,
        kind: PointerKind, // Borrow or BorrowMut
        source: VReg,
    },

    /// Dereference a pointer to get its value
    PointerDeref {
        dest: VReg,
        pointer: VReg,
        kind: PointerKind,
    },

    // =========================================================================
    // Interpreter fallback instructions (will be removed once all codegen implemented)
    // =========================================================================
    /// Call interpreter for a function that can't be compiled yet.
    /// This is a temporary fallback - will be removed once all features have native codegen.
    InterpCall {
        dest: Option<VReg>,
        func_name: String,
        args: Vec<VReg>,
    },

    /// Evaluate an expression via interpreter fallback.
    /// Temporary - will be removed once all expressions have native codegen.
    InterpEval { dest: VReg, expr_index: u32 },

    // =========================================================================
    // Collection instructions
    // =========================================================================
    /// Create an array literal from elements
    ArrayLit { dest: VReg, elements: Vec<VReg> },

    /// Create a tuple literal from elements
    TupleLit { dest: VReg, elements: Vec<VReg> },

    /// Create a SIMD vector literal from elements
    VecLit { dest: VReg, elements: Vec<VReg> },

    /// SIMD vector reduction: sum all lanes
    VecSum { dest: VReg, source: VReg },

    /// SIMD vector reduction: product of all lanes
    VecProduct { dest: VReg, source: VReg },

    /// SIMD vector reduction: minimum of all lanes
    VecMin { dest: VReg, source: VReg },

    /// SIMD vector reduction: maximum of all lanes
    VecMax { dest: VReg, source: VReg },

    /// SIMD vector reduction: all lanes are true (bool vector)
    VecAll { dest: VReg, source: VReg },

    /// SIMD vector reduction: any lane is true (bool vector)
    VecAny { dest: VReg, source: VReg },

    /// SIMD lane extract: v[idx] -> element
    VecExtract { dest: VReg, vector: VReg, index: VReg },

    /// SIMD lane insert: v.with(idx, val) -> new vector with lane replaced
    VecWith {
        dest: VReg,
        vector: VReg,
        index: VReg,
        value: VReg,
    },

    /// SIMD element-wise sqrt
    VecSqrt { dest: VReg, source: VReg },

    /// SIMD element-wise abs
    VecAbs { dest: VReg, source: VReg },

    /// SIMD element-wise floor
    VecFloor { dest: VReg, source: VReg },

    /// SIMD element-wise ceil
    VecCeil { dest: VReg, source: VReg },

    /// SIMD element-wise round
    VecRound { dest: VReg, source: VReg },

    /// SIMD shuffle: reorder lanes within a single vector
    VecShuffle {
        dest: VReg,
        source: VReg,
        /// Indices array register (contains lane indices)
        indices: VReg,
    },

    /// SIMD blend: merge two vectors using an indices array
    /// Indices 0..N select from first vector, N..2N from second
    VecBlend {
        dest: VReg,
        first: VReg,
        second: VReg,
        /// Indices array register
        indices: VReg,
    },

    /// SIMD masked select: mask.select(a, b) -> select from a where true, b where false
    VecSelect {
        dest: VReg,
        /// Bool mask vector
        mask: VReg,
        /// Values to select where mask is true
        if_true: VReg,
        /// Values to select where mask is false
        if_false: VReg,
    },

    /// SIMD load from array: f32x4.load(arr, offset) -> vec
    VecLoad {
        dest: VReg,
        /// Array to load from
        array: VReg,
        /// Offset into array
        offset: VReg,
    },

    /// SIMD store to array: v.store(arr, offset)
    VecStore {
        /// Vector to store
        source: VReg,
        /// Array to store into
        array: VReg,
        /// Offset into array
        offset: VReg,
    },

    /// SIMD gather (indexed load): f32x4.gather(arr, indices) -> vec
    VecGather {
        dest: VReg,
        /// Array to gather from
        array: VReg,
        /// Index vector
        indices: VReg,
    },

    /// SIMD scatter (indexed store): v.scatter(arr, indices)
    VecScatter {
        /// Vector to scatter
        source: VReg,
        /// Array to scatter into
        array: VReg,
        /// Index vector
        indices: VReg,
    },

    /// SIMD fused multiply-add: a.fma(b, c) -> a * b + c
    VecFma {
        dest: VReg,
        a: VReg,
        b: VReg,
        c: VReg,
    },

    /// SIMD reciprocal: v.recip() -> 1.0 / v
    VecRecip { dest: VReg, source: VReg },

    /// SIMD masked load: f32x4.load_masked(arr, offset, mask, default) -> vec
    VecMaskedLoad {
        dest: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
        default: VReg,
    },

    /// SIMD masked store: v.store_masked(arr, offset, mask)
    VecMaskedStore {
        source: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
    },

    /// SIMD element-wise minimum: a.min(b) -> element-wise min of two vectors
    VecMinVec { dest: VReg, a: VReg, b: VReg },

    /// SIMD element-wise maximum: a.max(b) -> element-wise max of two vectors
    VecMaxVec { dest: VReg, a: VReg, b: VReg },

    /// SIMD clamp: v.clamp(lo, hi) -> element-wise clamp to range
    VecClamp {
        dest: VReg,
        source: VReg,
        lo: VReg,
        hi: VReg,
    },

    /// GPU atomic operation: add, sub, min, max, and, or, xor, exchange
    /// Returns the old value at the location
    GpuAtomic {
        dest: VReg,
        /// Operation type
        op: GpuAtomicOp,
        /// Pointer to atomic location
        ptr: VReg,
        /// Value to combine
        value: VReg,
    },

    /// GPU atomic compare exchange: gpu.atomic_compare_exchange(ptr, expected, desired)
    /// Returns (old_value, success_bool)
    GpuAtomicCmpXchg {
        dest: VReg,
        /// Pointer to atomic location
        ptr: VReg,
        /// Expected value
        expected: VReg,
        /// Desired new value
        desired: VReg,
    },

    /// Create a dictionary literal from key-value pairs
    DictLit {
        dest: VReg,
        keys: Vec<VReg>,
        values: Vec<VReg>,
    },

    /// Get an element from a collection by index
    IndexGet {
        dest: VReg,
        collection: VReg,
        index: VReg,
    },

    /// Set an element in a collection by index
    IndexSet {
        collection: VReg,
        index: VReg,
        value: VReg,
    },

    /// Create a slice of a collection
    SliceOp {
        dest: VReg,
        collection: VReg,
        start: Option<VReg>,
        end: Option<VReg>,
        step: Option<VReg>,
    },

    /// Spread/unpack a collection into multiple values
    Spread { dest: VReg, source: VReg },

    /// Create a constant string
    ConstString { dest: VReg, value: String },

    /// Create a symbol
    ConstSymbol { dest: VReg, value: String },

    /// Format string interpolation
    FStringFormat { dest: VReg, parts: Vec<FStringPart> },

    // =========================================================================
    // Closure instructions (Phase 3)
    // =========================================================================
    /// Create a closure with captured variables (zero-cost: typed struct allocation)
    ClosureCreate {
        dest: VReg,
        /// Function name for direct call
        func_name: String,
        /// Total closure size: 8 (fn_ptr) + sum of capture sizes
        closure_size: u32,
        /// Byte offsets for each capture (first capture at offset 8)
        capture_offsets: Vec<u32>,
        /// Types of captured variables (for correct store instruction)
        capture_types: Vec<TypeId>,
        /// Captured variable values
        captures: Vec<VReg>,
    },

    /// Indirect call through a closure or function pointer (zero-cost: load + indirect call)
    IndirectCall {
        dest: Option<VReg>,
        /// The closure/function pointer to call
        callee: VReg,
        /// Parameter types for the call signature
        param_types: Vec<TypeId>,
        /// Return type
        return_type: TypeId,
        /// Arguments to pass
        args: Vec<VReg>,
        /// Effect annotation for the call
        effect: Effect,
    },

    // =========================================================================
    // Object/Method instructions (Phase 4)
    // =========================================================================
    /// Initialize a struct/class instance (zero-cost: inline allocation + stores)
    StructInit {
        dest: VReg,
        /// Type ID for the struct
        type_id: TypeId,
        /// Total struct size in bytes (for allocation)
        struct_size: u32,
        /// Byte offsets for each field (for direct stores)
        field_offsets: Vec<u32>,
        /// Field types (for correct store instruction)
        field_types: Vec<TypeId>,
        /// Field values in declaration order
        field_values: Vec<VReg>,
    },

    /// Get a field from an object (zero-cost: pointer arithmetic + load)
    FieldGet {
        dest: VReg,
        object: VReg,
        /// Byte offset from object pointer (computed at compile time)
        byte_offset: u32,
        /// Field type (for correct load instruction)
        field_type: TypeId,
    },

    /// Set a field on an object (zero-cost: pointer arithmetic + store)
    FieldSet {
        object: VReg,
        /// Byte offset from object pointer (computed at compile time)
        byte_offset: u32,
        /// Field type (for correct store instruction)
        field_type: TypeId,
        value: VReg,
    },

    /// Static method call (zero-cost: direct function call)
    /// Receiver type is known at compile time, so we can call directly.
    MethodCallStatic {
        dest: Option<VReg>,
        receiver: VReg,
        /// Direct function name (Type::method format)
        func_name: String,
        /// Arguments (not including receiver)
        args: Vec<VReg>,
    },

    /// Virtual method call (vtable-based dispatch for dyn types)
    /// Only used when receiver type is unknown at compile time.
    MethodCallVirtual {
        dest: Option<VReg>,
        receiver: VReg,
        /// Vtable slot index (computed at compile time)
        vtable_slot: u32,
        /// Method signature for indirect call
        param_types: Vec<TypeId>,
        return_type: TypeId,
        /// Arguments (not including receiver)
        args: Vec<VReg>,
    },

    /// Built-in method call (e.g., array.push, string.len)
    BuiltinMethod {
        dest: Option<VReg>,
        receiver: VReg,
        /// Type of the receiver (for dispatch)
        receiver_type: String,
        /// Method name
        method: String,
        /// Arguments (not including receiver)
        args: Vec<VReg>,
    },

    // =========================================================================
    // Pattern matching instructions (Phase 5)
    // =========================================================================
    /// Test if a value matches a pattern
    PatternTest {
        dest: VReg,
        subject: VReg,
        pattern: MirPattern,
    },

    /// Bind variables from a pattern match
    PatternBind {
        dest: VReg,
        subject: VReg,
        /// Binding path within the pattern
        binding: PatternBinding,
    },

    /// Get enum discriminant (variant index)
    EnumDiscriminant { dest: VReg, value: VReg },

    /// Get enum payload
    EnumPayload { dest: VReg, value: VReg },

    /// Create a unit enum variant (no payload)
    EnumUnit {
        dest: VReg,
        /// Enum type name
        enum_name: String,
        /// Variant name
        variant_name: String,
    },

    /// Create an enum variant with payload
    EnumWith {
        dest: VReg,
        /// Enum type name
        enum_name: String,
        /// Variant name
        variant_name: String,
        /// Payload value
        payload: VReg,
    },

    // =========================================================================
    // Union type instructions
    // =========================================================================
    /// Get the discriminant (type index) of a union value
    UnionDiscriminant { dest: VReg, value: VReg },

    /// Extract the payload value from a union
    UnionPayload {
        dest: VReg,
        value: VReg,
        /// Expected type index (for type safety)
        type_index: usize,
    },

    /// Wrap a value into a union type
    UnionWrap {
        dest: VReg,
        /// The value to wrap
        value: VReg,
        /// Index of the type in the union's variant list
        type_index: usize,
    },

    // =========================================================================
    // Async/Generator instructions (Phase 6)
    // =========================================================================
    /// Create a future
    FutureCreate {
        dest: VReg,
        /// Block containing the async body
        body_block: BlockId,
    },

    /// Await a future
    Await { dest: VReg, future: VReg },

    /// Spawn an actor
    ActorSpawn {
        dest: VReg,
        /// Block containing the actor body
        body_block: BlockId,
    },

    /// Send a message to an actor
    ActorSend { actor: VReg, message: VReg },

    /// Receive a message from the current actor's mailbox
    ActorRecv { dest: VReg },

    /// Join an actor, waiting for it to complete
    /// Returns 1 on success, 0 on failure
    ActorJoin { dest: VReg, actor: VReg },

    /// Reply to parent actor by sending a message
    /// Returns NIL (void operation)
    ActorReply { message: VReg },

    /// Create a generator
    GeneratorCreate {
        dest: VReg,
        /// Block containing the generator body
        body_block: BlockId,
    },

    /// Yield a value from a generator
    Yield { value: VReg },

    /// Get next value from a generator
    GeneratorNext { dest: VReg, generator: VReg },

    // =========================================================================
    // Error handling instructions (Phase 7)
    // =========================================================================
    /// Try to unwrap a Result/Option, branching on error
    TryUnwrap {
        dest: VReg,
        value: VReg,
        /// Block to jump to on error
        error_block: BlockId,
        /// Register to store error value
        error_dest: VReg,
    },

    /// Create Option::Some
    OptionSome { dest: VReg, value: VReg },

    /// Create Option::None
    OptionNone { dest: VReg },

    /// Create Result::Ok
    ResultOk { dest: VReg, value: VReg },

    /// Create Result::Err
    ResultErr { dest: VReg, value: VReg },

    // =========================================================================
    // Contract instructions (Design by Contract support)
    // =========================================================================
    /// Check a contract condition (precondition, postcondition, or invariant).
    /// Panics with contract violation error if condition is false.
    ContractCheck {
        /// The condition to check (should be boolean)
        condition: VReg,
        /// Type of contract being checked
        kind: ContractKind,
        /// Function name for error message
        func_name: String,
        /// Optional custom error message
        message: Option<String>,
    },

    /// Capture a value at function entry for use in postconditions with old().
    /// The captured value is stored in a temporary slot.
    ContractOldCapture {
        /// Destination for the captured value
        dest: VReg,
        /// The expression value to capture
        value: VReg,
    },

    // =========================================================================
    // Coverage instrumentation instructions
    // =========================================================================
    /// Record a decision evaluation for decision coverage.
    /// Tracks both true and false outcomes of boolean decisions (if/while/match guards).
    DecisionProbe {
        /// Unique ID of this decision within the function
        decision_id: u32,
        /// The decision result (boolean value)
        result: VReg,
        /// Source location for mapping back to source
        file: String,
        line: u32,
        column: u32,
    },

    /// Record a condition evaluation for condition/MC-DC coverage.
    /// Tracks individual conditions within compound boolean expressions.
    ConditionProbe {
        /// ID of the parent decision
        decision_id: u32,
        /// Unique ID of this condition within the decision
        condition_id: u32,
        /// The condition result (boolean value)
        result: VReg,
        /// Source location
        file: String,
        line: u32,
        column: u32,
    },

    /// Record block entry for path coverage.
    /// Tracks which execution paths are taken through functions.
    PathProbe {
        /// Unique ID of the execution path
        path_id: u32,
        /// ID of the current block in the path
        block_id: u32,
    },

    /// Check that a value is within the bounds of a unit type.
    /// In debug mode, panics if the value is out of range.
    /// In release mode, applies the overflow behavior (wrap, saturate, or no-op).
    UnitBoundCheck {
        /// The value to check
        value: VReg,
        /// Unit type name for error messages
        unit_name: String,
        /// Lower bound (inclusive)
        min: i64,
        /// Upper bound (inclusive)
        max: i64,
        /// Overflow behavior (default=panic in debug, no-op in release)
        overflow: UnitOverflowBehavior,
    },

    /// Widen a unit value to a larger representation.
    /// Example: u8 distance → u16 distance (lossless conversion)
    UnitWiden {
        /// Destination register (wider type)
        dest: VReg,
        /// Source value (narrow type)
        value: VReg,
        /// Source type bit width
        from_bits: u8,
        /// Destination type bit width
        to_bits: u8,
        /// Whether source is signed
        signed: bool,
    },

    /// Narrow a unit value to a smaller representation with bounds checking.
    /// Example: u16 distance → u8 distance (may overflow)
    UnitNarrow {
        /// Destination register (narrower type)
        dest: VReg,
        /// Source value (wide type)
        value: VReg,
        /// Source type bit width
        from_bits: u8,
        /// Destination type bit width
        to_bits: u8,
        /// Whether types are signed
        signed: bool,
        /// Overflow behavior
        overflow: UnitOverflowBehavior,
    },

    /// Saturate a unit value to its type bounds.
    /// Clamps the value to [min, max] without error.
    UnitSaturate {
        /// Destination register
        dest: VReg,
        /// Source value
        value: VReg,
        /// Minimum bound
        min: i64,
        /// Maximum bound
        max: i64,
    },

    // =========================================================================
    // GPU instructions (software backend + future hardware)
    // =========================================================================
    /// Get global work item ID for a dimension (0=x, 1=y, 2=z)
    GpuGlobalId { dest: VReg, dim: u8 },

    /// Get local work item ID within work group
    GpuLocalId { dest: VReg, dim: u8 },

    /// Get work group ID
    GpuGroupId { dest: VReg, dim: u8 },

    /// Get global work size (total work items)
    GpuGlobalSize { dest: VReg, dim: u8 },

    /// Get local work group size
    GpuLocalSize { dest: VReg, dim: u8 },

    /// Get number of work groups
    GpuNumGroups { dest: VReg, dim: u8 },

    /// Work group barrier (synchronize all work items in group)
    GpuBarrier,

    /// Memory fence (ensure memory ordering)
    GpuMemFence { scope: GpuMemoryScope },

    /// SIMD neighbor load: load from array at (this.index() +/- 1)
    NeighborLoad {
        dest: VReg,
        array: VReg,
        direction: NeighborDirection,
    },

    /// Allocate shared memory (work group local)
    GpuSharedAlloc {
        dest: VReg,
        element_type: TypeId,
        size: u32,
    },

    // =========================================================================
    // Parallel Iterator Instructions (#415)
    // =========================================================================

    /// Parallel map: applies a closure to each element in parallel
    /// `dest = par_map(input, closure)`
    ParMap {
        dest: VReg,
        input: VReg,
        closure: VReg,
        /// Backend preference: None = auto, Some = force specific backend
        backend: Option<ParallelBackend>,
    },

    /// Parallel reduce: combines elements using a binary operation
    /// `dest = par_reduce(input, initial, closure)`
    ParReduce {
        dest: VReg,
        input: VReg,
        initial: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    },

    /// Parallel filter: keeps elements matching predicate
    /// `dest = par_filter(input, predicate)`
    ParFilter {
        dest: VReg,
        input: VReg,
        predicate: VReg,
        backend: Option<ParallelBackend>,
    },

    /// Parallel for_each: executes closure for side effects
    /// `par_for_each(input, closure)`
    ParForEach {
        input: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    },
}
