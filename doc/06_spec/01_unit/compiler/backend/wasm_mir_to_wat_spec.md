# Wasm Mir To Wat Specification

> Tests covering MirToWat translation layer, coverage evidence probes, translate_const, emit_operand, translate_call, translate_binop, translate_binop float operands, translate_binop unknown operand type, translate_binop, translate_unaryop, translate_module end to end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Mir To Wat Specification

## Scenarios

### MirToWat translation layer

### coverage evidence probes

#### fails closed when a DecisionProbe reaches WAT translation

- fails closed when a DecisionProbe reaches WAT translation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a DecisionProbe reaches WAT translation")
val inst = MirInst(kind: MirInstKind.DecisionProbe(
    7, "decision:sha256", op_const(
        MirConstValue.Bool(true), ty(MirTypeKind.Bool)
    ), "src/example.spl", 12, 0
), span: nil)
val wat = instruction_wat(inst)

expect(wat).to_contain("unlowered DecisionProbe 'decision:sha256'")
expect(wat).to_contain("unreachable")
assert_false(wat.contains(";; unhandled instruction"))
```

</details>

#### fails closed when a ConditionProbe reaches WAT translation

- fails closed when a ConditionProbe reaches WAT translation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a ConditionProbe reaches WAT translation")
val inst = MirInst(kind: MirInstKind.ConditionProbe(
    8, "condition:sha256", 7, "decision:sha256", op_const(
        MirConstValue.Bool(false), ty(MirTypeKind.Bool)
    ), "src/example.spl", 12, 4
), span: nil)
val wat = instruction_wat(inst)

expect(wat).to_contain("unlowered ConditionProbe 'condition:sha256'")
expect(wat).to_contain("unreachable")
assert_false(wat.contains(";; unhandled instruction"))
```

</details>

### translate_const

#### writes the destination local for a scalar Zero constant

- writes the destination local for a scalar Zero constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes the destination local for a scalar Zero constant")
# REGRESSION: `Zero` is the real MirConstValue variant, but
# translate_const only had dead `Unit`/`Nil` arms, so Zero fell to
# `case _:` which emitted a comment and NO local.set -- leaving the
# destination local unwritten with no diagnostic.
val b = builder()
translator().translate_const(b, local(0), MirConstValue.Zero, ty(MirTypeKind.I64))
val wat = b.build()

expect(wat).to_contain("i64.const 0")
expect(wat).to_contain("local.set $_l0")
```

</details>

#### zero-initializes at the destination width, not always i64

- zero-initializes at the destination width, not always i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-initializes at the destination width, not always i64")
val b = builder()
translator().translate_const(b, local(1), MirConstValue.Zero, ty(MirTypeKind.I32))
val wat = b.build()

expect(wat).to_contain("i32.const 0")
expect(wat).to_contain("local.set $_l1")
```

</details>

#### emits an integer constant and stores it

- emits an integer constant and stores it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an integer constant and stores it")
val b = builder()
translator().translate_const(b, local(2), MirConstValue.Int(42), ty(MirTypeKind.I64))
val wat = b.build()

expect(wat).to_contain("i64.const 42")
expect(wat).to_contain("local.set $_l2")
```

</details>

#### traps on an aggregate constant instead of emitting malformed WAT

- traps on an aggregate constant instead of emitting malformed WAT


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on an aggregate constant instead of emitting malformed WAT")
# The old Array arm emitted `i64.const {elem}` -- interpolating a
# MirConstValue into a numeric operand. Unsupported must fail
# explicitly, never produce a plausible-looking instruction.
val b = builder()
val elems = [MirConstValue.Int(1), MirConstValue.Int(2)]
translator().translate_const(b, local(3), MirConstValue.Array(elems), ty(MirTypeKind.I64))
val wat = b.build()

expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
```

</details>

### emit_operand

#### pushes a local for a Copy operand

- pushes a local for a Copy operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes a local for a Copy operand")
# REGRESSION: emit_operand matched the MirOperand STRUCT instead of
# `.kind`, so every operand fell to a comment-only default and
# pushed NOTHING onto the value stack.
val b = builder()
translator().emit_operand(b, MirOperand(kind: MirOperandKind.Copy(local(4))))
expect(b.build()).to_contain("local.get $_l4")
```

</details>

#### pushes a local for a Move operand

- pushes a local for a Move operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes a local for a Move operand")
val b = builder()
translator().emit_operand(b, MirOperand(kind: MirOperandKind.Move(local(5))))
expect(b.build()).to_contain("local.get $_l5")
```

</details>

#### pushes a real constant, not a comment, for a Const operand

- pushes a real constant, not a comment, for a Const operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes a real constant, not a comment, for a Const operand")
val b = builder()
translator().emit_operand(b, op_const(MirConstValue.Int(7), ty(MirTypeKind.I64)))
expect(b.build()).to_contain("i64.const 7")
```

</details>

#### pushes a bool constant as i32

- pushes a bool constant as i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes a bool constant as i32")
val b = builder()
translator().emit_operand(b, op_const(MirConstValue.Bool(true), ty(MirTypeKind.Bool)))
expect(b.build()).to_contain("i32.const 1")
```

</details>

### translate_call

#### emits the call instruction for a symbol callee

- emits the call instruction for a symbol callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the call instruction for a symbol callee")
# REGRESSION: translate_call matched the struct against
# `Constant`/`Use` with no `case _:`, so it emitted the argument
# pushes and then NO call at all -- the following local.set
# consumed the last argument as if it were the return value.
val b = builder()
val callee = op_const(MirConstValue.Str("my_func"), ty(MirTypeKind.I32))
val args = [op_const(MirConstValue.Int(3), ty(MirTypeKind.I64))]
translator().translate_call(b, local(6), callee, args)
val wat = b.build()

expect(wat).to_contain("i64.const 3")
expect(wat).to_contain("call $my_func")
```

</details>

#### emits call_indirect for a computed callee

- emits call_indirect for a computed callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits call_indirect for a computed callee")
val b = builder()
val callee = MirOperand(kind: MirOperandKind.Move(local(7)))
translator().translate_call(b, local(8), callee, [])
val wat = b.build()

expect(wat).to_contain("local.get $_l7")
expect(wat).to_contain("call_indirect")
```

</details>

### translate_binop

#### emits i64.and for BitAnd instead of the swallowed i32.and

- emits i64.and for BitAnd instead of the swallowed i32.and


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64.and for BitAnd instead of the swallowed i32.and")
expect(binop_wat(MirBinOp.BitAnd)).to_contain("i64.and")
```

</details>

#### emits i64.or for BitOr

- emits i64.or for BitOr


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64.or for BitOr")
expect(binop_wat(MirBinOp.BitOr)).to_contain("i64.or")
```

</details>

#### emits i64.xor for BitXor

- emits i64.xor for BitXor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64.xor for BitXor")
expect(binop_wat(MirBinOp.BitXor)).to_contain("i64.xor")
```

</details>

#### emits i64.shl for Shl

- emits i64.shl for Shl


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64.shl for Shl")
expect(binop_wat(MirBinOp.Shl)).to_contain("i64.shl")
```

</details>

#### emits an arithmetic right shift for Shr

- emits an arithmetic right shift for Shr


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an arithmetic right shift for Shr")
expect(binop_wat(MirBinOp.Shr)).to_contain("i64.shr_s")
```

</details>

#### keeps the already-reachable arms working

- keeps the already-reachable arms working


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the already-reachable arms working")
expect(binop_wat(MirBinOp.Add)).to_contain("i64.add")
expect(binop_wat(MirBinOp.Ge)).to_contain("i64.ge_s")
```

</details>

#### lowers Offset as unscaled pointer arithmetic

- lowers Offset as unscaled pointer arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers Offset as unscaled pointer arithmetic")
expect(binop_wat(MirBinOp.Offset)).to_contain("i64.add")
```

</details>

#### traps on Pow rather than emitting a comment and no result

- traps on Pow rather than emitting a comment and no result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on Pow rather than emitting a comment and no result")
# The old Pow arm re-pushed both operands (already on the stack),
# converted them, then emitted only a comment -- four values left
# on the value stack and no result produced.
val wat = binop_wat(MirBinOp.Pow)
expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
```

</details>

#### traps on MatMul

- traps on MatMul


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on MatMul")
val wat = binop_wat(MirBinOp.MatMul)
expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
```

</details>

#### traps on every Broadcast op instead of emitting a bitwise and

- traps on every Broadcast op instead of emitting a bitwise and


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on every Broadcast op instead of emitting a bitwise and")
for op in [MirBinOp.BroadcastAdd, MirBinOp.BroadcastSub,
           MirBinOp.BroadcastMul, MirBinOp.BroadcastDiv,
           MirBinOp.BroadcastPow]:
    val wat = binop_wat(op)
    expect(wat).to_contain("UNSUPPORTED")
    expect(wat).to_contain("unreachable")
```

</details>

#### picks the operand type from a Const operand without any registration

- picks the operand type from a Const operand without any registration


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("picks the operand type from a Const operand without any registration")
# MirOperandKind.Const carries its own MirType, so a constant
# operand is self-describing -- no local registration needed.
val b = builder()
val lhs = op_const(MirConstValue.Float(1.5), ty(MirTypeKind.F64))
val rhs = op_const(MirConstValue.Float(2.5), ty(MirTypeKind.F64))
translator().translate_binop(b, local(20), MirBinOp.Add, lhs, rhs)
val wat = b.build()

expect(wat).to_contain("f64.add")
assert_false(wat.contains("i64.add"))
```

</details>

### translate_binop float operands

#### emits f64.add, not i64.add, for a float Add

- emits f64.add, not i64.add, for a float Add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64.add, not i64.add, for a float Add")
val wat = binop_wat_ty(MirTypeKind.F64, MirBinOp.Add)
expect(wat).to_contain("f64.add")
assert_false(wat.contains("i64.add"))
```

</details>

#### emits f64.sub for a float Sub

- emits f64.sub for a float Sub


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64.sub for a float Sub")
val wat = binop_wat_ty(MirTypeKind.F64, MirBinOp.Sub)
expect(wat).to_contain("f64.sub")
assert_false(wat.contains("i64.sub"))
```

</details>

#### emits f64.mul for a float Mul

- emits f64.mul for a float Mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64.mul for a float Mul")
val wat = binop_wat_ty(MirTypeKind.F64, MirBinOp.Mul)
expect(wat).to_contain("f64.mul")
assert_false(wat.contains("i64.mul"))
```

</details>

#### emits f64.div with no signedness suffix

- emits f64.div with no signedness suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64.div with no signedness suffix")
# Float division is `f64.div`; there is no `f64.div_s`. Reusing the
# integer arm would have produced `i64.div_s`, which is both the
# wrong domain and a suffix that does not exist for floats.
val wat = binop_wat_ty(MirTypeKind.F64, MirBinOp.Div)
expect(wat).to_contain("f64.div")
assert_false(wat.contains("div_s"))
```

</details>

#### emits unsuffixed float comparisons

- emits unsuffixed float comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits unsuffixed float comparisons")
expect(binop_wat_ty(MirTypeKind.F64, MirBinOp.Eq)).to_contain("f64.eq")
expect(binop_wat_ty(MirTypeKind.F64, MirBinOp.Ne)).to_contain("f64.ne")
expect(binop_wat_ty(MirTypeKind.F64, MirBinOp.Lt)).to_contain("f64.lt")
expect(binop_wat_ty(MirTypeKind.F64, MirBinOp.Le)).to_contain("f64.le")
expect(binop_wat_ty(MirTypeKind.F64, MirBinOp.Gt)).to_contain("f64.gt")
expect(binop_wat_ty(MirTypeKind.F64, MirBinOp.Ge)).to_contain("f64.ge")
```

</details>

#### never emits a signed integer compare for a float compare

- never emits a signed integer compare for a float compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never emits a signed integer compare for a float compare")
for op in [MirBinOp.Lt, MirBinOp.Le, MirBinOp.Gt, MirBinOp.Ge]:
    val wat = binop_wat_ty(MirTypeKind.F64, op)
    assert_false(wat.contains("_s"))
    assert_false(wat.contains("i64."))
```

</details>

#### lowers f32 at its own width, not widened to f64

- lowers f32 at its own width, not widened to f64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers f32 at its own width, not widened to f64")
val wat = binop_wat_ty(MirTypeKind.F32, MirBinOp.Mul)
expect(wat).to_contain("f32.mul")
assert_false(wat.contains("f64."))
```

</details>

#### traps on float Rem -- wasm has no float remainder instruction

- traps on float Rem -- wasm has no float remainder instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on float Rem -- wasm has no float remainder instruction")
val wat = binop_wat_ty(MirTypeKind.F64, MirBinOp.Rem)
expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
assert_false(wat.contains("rem_s"))
```

</details>

#### traps on bitwise and shift ops applied to float operands

- traps on bitwise and shift ops applied to float operands


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on bitwise and shift ops applied to float operands")
for op in [MirBinOp.BitAnd, MirBinOp.BitOr, MirBinOp.BitXor,
           MirBinOp.Shl, MirBinOp.Shr]:
    val wat = binop_wat_ty(MirTypeKind.F64, op)
    expect(wat).to_contain("UNSUPPORTED")
    expect(wat).to_contain("unreachable")
```

</details>

#### lowers integer ops at i32 width when the operands are i32

- lowers integer ops at i32 width when the operands are i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers integer ops at i32 width when the operands are i32")
# The same missing-type defect: i32 operands were pushed as
# `i32.const` and then combined with `i64.add`.
val wat = binop_wat_ty(MirTypeKind.I32, MirBinOp.Add)
expect(wat).to_contain("i32.add")
assert_false(wat.contains("i64.add"))
```

</details>

### translate_binop unknown operand type

#### traps instead of guessing an integer op when no type is known

- traps instead of guessing an integer op when no type is known


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps instead of guessing an integer op when no type is known")
# THE core requirement. An unregistered local has no type. Emitting
# `i64.add` here -- a plausible-looking instruction for a type we
# never established -- is exactly the failure mode being fixed.
val b = builder()
translator().translate_binop(b, local(20), MirBinOp.Add, op_local(0), op_local(1))
val wat = b.build()

expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
assert_false(wat.contains("i64.add"))
assert_false(wat.contains("f64.add"))
```

</details>

#### traps for a type with no scalar WAT arithmetic form

- traps for a type with no scalar WAT arithmetic form


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps for a type with no scalar WAT arithmetic form")
# Unit/aggregates/SIMD have no arithmetic lowering here. The
# classifier must NOT reuse mir_type_to_wasm_type, whose `case _:`
# silently answers i32 for anything unrecognised.
val b = builder()
val t = MirToWat.create("spec_mod")
t.register_local_types([mk_local(0, MirTypeKind.Unit), mk_local(1, MirTypeKind.Unit)])
t.translate_binop(b, local(20), MirBinOp.Add, op_local(0), op_local(1))
val wat = b.build()

expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
assert_false(wat.contains("i32.add"))
```

</details>

#### traps on mismatched operand types rather than reinterpreting one

- traps on mismatched operand types rather than reinterpreting one


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on mismatched operand types rather than reinterpreting one")
val b = builder()
val t = MirToWat.create("spec_mod")
t.register_local_types([mk_local(0, MirTypeKind.F64), mk_local(1, MirTypeKind.I64)])
t.translate_binop(b, local(20), MirBinOp.Add, op_local(0), op_local(1))
val wat = b.build()

expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
```

</details>

#### does not leak one function's local types into the next

- does not leak one function's local types into the next


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not leak one function's local types into the next")
val t = MirToWat.create("spec_mod")
t.register_local_types([mk_local(0, MirTypeKind.F64), mk_local(1, MirTypeKind.F64)])
t.register_local_types([mk_local(0, MirTypeKind.I64), mk_local(1, MirTypeKind.I64)])
val b = builder()
t.translate_binop(b, local(20), MirBinOp.Add, op_local(0), op_local(1))

expect(b.build()).to_contain("i64.add")
assert_false(b.build().contains("f64.add"))
```

</details>

### translate_binop

#### never emits i32.and for an op that is not a bitwise and

- never emits i32.and for an op that is not a bitwise and


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never emits i32.and for an op that is not a bitwise and")
# The single sharpest pin on the defect: i32.and was the swallowing
# arm's instruction and is not the correct lowering for ANY
# MirBinOp variant, so it must not appear at all.
for op in [MirBinOp.Pow, MirBinOp.MatMul, MirBinOp.BitAnd,
           MirBinOp.BitOr, MirBinOp.BitXor, MirBinOp.Shl,
           MirBinOp.Shr, MirBinOp.Offset]:
    assert_false(binop_wat(op).contains("i32.and"))
```

</details>

### translate_unaryop

#### emits a bitwise complement for BitNot, not f64.neg

- emits a bitwise complement for BitNot, not f64.neg


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a bitwise complement for BitNot, not f64.neg")
val wat = unaryop_wat(MirUnaryOp.BitNot)
expect(wat).to_contain("i64.const -1")
expect(wat).to_contain("i64.xor")
assert_false(wat.contains("f64.neg"))
```

</details>

#### traps on Transpose instead of negating a float

- traps on Transpose instead of negating a float


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on Transpose instead of negating a float")
val wat = unaryop_wat(MirUnaryOp.Transpose)
expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
assert_false(wat.contains("f64.neg"))
```

</details>

#### keeps Neg and Not working

- keeps Neg and Not working


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Neg and Not working")
expect(unaryop_wat(MirUnaryOp.Neg)).to_contain("i64.sub")
expect(unaryop_wat_ty(MirTypeKind.Bool, MirUnaryOp.Not)).to_contain("i32.eqz")
```

</details>

#### emits f64.neg for a float Neg instead of an integer subtract

- emits f64.neg for a float Neg instead of an integer subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64.neg for a float Neg instead of an integer subtract")
# MirUnaryOp carries no operand type either, so Neg had the same
# defect: `i64.const 0; <x>; i64.sub` on an f64 operand.
val wat = unaryop_wat_ty(MirTypeKind.F64, MirUnaryOp.Neg)
expect(wat).to_contain("f64.neg")
assert_false(wat.contains("i64.sub"))
assert_false(wat.contains("i64.const 0"))
```

</details>

#### emits f32.neg at f32 width

- emits f32.neg at f32 width


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f32.neg at f32 width")
expect(unaryop_wat_ty(MirTypeKind.F32, MirUnaryOp.Neg)).to_contain("f32.neg")
```

</details>

#### traps on a bitwise not applied to a float operand

- traps on a bitwise not applied to a float operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps on a bitwise not applied to a float operand")
val wat = unaryop_wat_ty(MirTypeKind.F64, MirUnaryOp.BitNot)
expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
assert_false(wat.contains("i64.xor"))
```

</details>

#### traps when the unaryop operand type is unknown

- traps when the unaryop operand type is unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("traps when the unaryop operand type is unknown")
val b = builder()
translator().translate_unaryop(b, local(21), MirUnaryOp.Neg, op_local(0))
val wat = b.build()

expect(wat).to_contain("UNSUPPORTED")
expect(wat).to_contain("unreachable")
assert_false(wat.contains("i64.sub"))
```

</details>

### translate_module end to end

#### translates a whole float function without aborting

- translates a whole float function without aborting


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates a whole float function without aborting")
val wat = MirToWat.create("float_mod").translate_module(float_fn_module())
expect(wat).to_contain("(func $fmul")
```

</details>

#### declares float params and result at f64, named to match the body

- declares float params and result at f64, named to match the body


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares float params and result at f64, named to match the body")
val wat = MirToWat.create("float_mod").translate_module(float_fn_module())
# Params must be named $_lN: every instruction lowering references
# locals as `_l{id}`, so naming params from MirLocal.name produced
# parameters no body instruction could ever resolve.
expect(wat).to_contain("(param $_l0 f64)")
expect(wat).to_contain("(param $_l1 f64)")
expect(wat).to_contain("(result f64)")
expect(wat).to_contain("(local $_l2 f64)")
```

</details>

#### emits f64.mul in the function body, not i64.mul

- emits f64.mul in the function body, not i64.mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64.mul in the function body, not i64.mul")
val wat = MirToWat.create("float_mod").translate_module(float_fn_module())
expect(wat).to_contain("f64.mul")
assert_false(wat.contains("i64.mul"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MirToWat translation layer, coverage evidence probes, translate_const, emit_operand, translate_call, translate_binop, translate_binop float operands, translate_binop unknown operand type, translate_binop, translate_unaryop, translate_module end to end.
- MirToWat translation layer
- coverage evidence probes
- translate_const
- emit_operand
- translate_call
- translate_binop
- translate_binop float operands
- translate_binop unknown operand type
- translate_binop
- translate_unaryop
- translate_module end to end

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae1619ffe3d262d8678998249b83d878816537d78db7be3b4431602eb45bdac7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae1619ffe3d262d8678998249b83d878816537d78db7be3b4431602eb45bdac7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae1619ffe3d262d8678998249b83d878816537d78db7be3b4431602eb45bdac7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/wasm_mir_to_wat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/wasm_mir_to_wat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/wasm_mir_to_wat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when a DecisionProbe reaches WAT translation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when a ConditionProbe reaches WAT translation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes the destination local for a scalar Zero constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
