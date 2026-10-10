# Tagged plugin bare-unit OR owner workaround

AUTHORED_UNEXECUTED. The exact a0/aa404 full Phase3 baseline accepted1142HIRmodules and rejected18; these six plugin files contribute33 OR-binding diagnostics. Explicit unit-owner qualification is a temporary source workaround, not a permanent compiler repair. The original legal bare forms remain in a real-owner reproducer. No payload binding collector or guards/bodies are modified.

Actual declaration/caller proof:

## LocalKind

src/compiler/50.mir/mir_types.spl:33

```simple
enum LocalKind:
    Arg(index: i64)     # Function argument
    Var                  # Regular variable
    Temp                 # Temporary (SSA)
    Return               # Return slot

struct MirLocal:
```

## MirTypeKind

src/compiler/50.mir/mir_types.spl:150

```simple
enum MirTypeKind:
    # Primitives
    I8, I16, I32, I64
    U8, U16, U32, U64
    F32, F64
    Bool
    Char
    Unit

    # SIMD vector types
    Vec4f     # 4x f32 (128-bit SSE/NEON)
```

## MirBinOp

src/compiler/50.mir/mir_instruction_support.spl:215

```simple
enum MirBinOp:
    # Arithmetic
    Add, Sub, Mul, Div, Rem
    Pow                         # **
    # Matrix operations
    MatMul                      # @
    # Bitwise
    BitAnd, BitOr, BitXor, Shl, Shr
    # Comparison
    Eq, Ne, Lt, Le, Gt, Ge
    # Broadcast operations (dotted operators)
```

## PrimitiveType

src/compiler/70.backend/backend/common/type_mapper.spl:226

```simple
enum PrimitiveType:
    I64
    I32
    I16
    I8
    U64     # Unsigned types for GPU
    U32
    U16
    U8
    F64
    F32
    F16     # Half precision (GPU)
    Bool
    Unit

enum Mutability:
    Mutable
```


The native bare/qualified fixtures exercise every listed alternative and nonmember on actual compiler enum declarations. The actual MirTypeKind.Opaque payload x/y mismatch must remain a named rejection/no object; unrelated errors cannot count as rejection PASS. All three are UNEXECUTED. Permanent diagnosis remains contextual unit-owner propagation/registration; these source-only proofs do not establish the precise runtime first loss.
