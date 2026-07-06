# LLVM Pointer Return Null Spec

Source: `test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl`

## LLVM pointer return null

Verifies that MIR-to-LLVM return lowering emits LLVM's pointer null literal for
pointer-typed zero returns. It also verifies that string globals are mirrored
into the text accumulator used by the bootstrap flush path, and that the
libLLVM backend routes pointer-typed integer zero constants through the LLVM
null constant path.

Checked evidence:

```text
ret ptr null
```

Rejected evidence:

```text
ret ptr 0
```

Latest focused evidence:

```text
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
3 examples, 0 failures
```
