# Redeploy Kit 02 — closure returned across function boundary = invalid heap

## Defect (memory-safety, critical)
A closure created inside a function, capturing that function's parameter, and
returned to the caller prints `<invalid-heap:0x69>` instead of `105`.

```
fn make_adder(base: i64):
    val add_base = \x: x + base
    return add_base
fn main():
    val adder = make_adder(100)
    print(adder(5))   # expected 105, actual <invalid-heap:0x69>
```

## Root cause (analysis — not yet fixed)
Decisive evidence: `0x69 == 105`. The closure body computed the correct integer
value 105 (base=100 captured correctly, 5+100). The corruption is a **tag/boxing
mismatch at the closure-call return boundary**, not a wrong computation.

The `run` path executes via the Rust seed's cranelift JIT
(`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`). In
`compile_indirect_call` the callee signature return type comes from
`type_id_to_cranelift(return_type)`:

```rust
if return_type != TypeId::VOID {
    sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
}
```

When the closure escapes its defining function (`return add_base`), its concrete
return type is erased to an opaque/`any` type. At the call site `adder(5)` the
result is then treated as an already-boxed `RuntimeValue` (heap-tagged), but the
JIT'd closure body actually returns a **native unboxed i64** (105). The raw
value 105 is handed to `print` without `rt_box_int`/`from_int`; `print` reads
raw bits `0x69`, whose NaN-box tag bits are 0 → interpreted as a heap pointer →
`<invalid-heap:0x69>`.

Fix direction (requires seed rebuild to verify): make the closure ABI consistent
across the boundary — either (a) always box closure return values (canonical
`RuntimeValue` closure calling convention) when the static return type is
unknown/erased, and unbox at the call site per the declared type; or (b)
propagate the closure's concrete return `TypeId` through the escaping-closure
type so `compile_indirect_call` emits the matching boxing. Option (a) is the
memory-safe default and matches how other erased-type values flow.

## Test plan
- Expected-behavior spec:
  `test/cert/redeploy_pending/closure_return_across_function_boundary.spl`
  (expects `105`).
- After the ABI fix + seed rebuild, this spec should print `105`, exit 0.

## Verify-now vs redeploy-pending
- REDEPLOY-PENDING + NOT-YET-FIXED: root cause identified (boxing mismatch at the
  escaping-closure return boundary); the codegen fix lives in the frozen Rust
  seed JIT and is not implemented in this change (fixing + rebuilding cranelift
  codegen was outside the verifiable scope of this session). Honestly flagged so
  no false "works" claim is made.
