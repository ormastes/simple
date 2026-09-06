# sdn_insert — SdnValue.empty_dict().insert() write is lost

Status: **DIAGNOSED, NOT FIXED.** Spec left RED exactly as found
(`test/01_unit/lib/common/sdn_coverage_spec.spl` — "get by key from dict",
51 examples / 1 failure on both engines, unchanged before and after).

## Verdict on the three candidates
- (a) mutating-method write loss — **true on the interpreter only**, but the
  "extract-mutate-write-back" remedy does NOT work: `fn insert(mut self, …)`
  with `self = SdnValue.Dict(tmp)` still does not propagate (probe11).
- (b) value-semantics copy — **true, and deeper than assumed**: the interpreter
  deep-copies the enum payload at the `case Dict(d)` binding, including a
  *class* payload (probe12), so no reference-payload workaround exists either.
- (c) logic bug in the dict store — **disproven**. `_sdn_dict_put` and the
  `insert`/`get` bodies are correct; both work on an inline `SdnValue.Dict({})`
  under the JIT (probe5 case D = green).

## Actual root causes (two, both compiler-level, both outside this module)
1. **JIT / default engine**: `EnumName.assoc_fn()` never calls the associated
   function. `E1.totally_undefined()` returns a bogus value with **no error**
   (probe10); `E1.mk()` matches no `case` arm (probe8, same file where the
   *class* static `Box.make()` works and a free fn works). Under
   `SIMPLE_EXECUTION_MODE=interpreter` the same call correctly raises
   `unknown variant or method`. So on the JIT `SdnValue.empty_dict()` is not a
   dict at all and both `insert` and `get` fall to `case _`.
2. **Interpreter**: enum associated fns work, but `case Dict(d)` binds a deep
   copy — `insert` returns true and `_sdn_dict_put` runs, yet `len()` stays 0
   (probe1 case E). Only a write-back performed in the *caller's* frame sticks
   (probe1 case F).

Reproduction is import-free and 12–60 lines: `build/sdnins_probe/probe{1,5,8,10,11,12}.spl`.
probe8 and probe10 are the two decisive ones.

## Attempts that did not fix it (all reverted, sources clean)
- `parser/src/types_def/enum_parsing.rs`: adding `TokenKind::Static` to the
  enum-body method check. **Unnecessary** — `static fn` in an enum body already
  parses; verified against the pre-change binary.
- `compiler/src/hir/lower/expr/{calls,mod}.rs`: routing `EnumName.member()` to
  `lower_static_member_call_with_sugar` when `member` is not a variant. Built
  and tested — **no behaviour change**, so the JIT call site is not
  `Expr::Identifier("Enum.member")`; the mis-lowering is elsewhere.

`src/compiler_rust/target/bootstrap/simple` was rebuilt from the reverted
sources, so it matches HEAD again.

## Next step
Fix must land in the compiler, not in `src/lib/common/sdn/value.spl`. Start at
the JIT/MIR call-site naming for `EnumName.assoc_fn` (`ctx.func_ids` lookup in
`compiler/src/codegen/instr/calls.rs` ~L3172 falls through silently; note
`module_pass.rs` ~L402 registers every `EnumName.method` as a **global**, which
is the likely hijacker). The interpreter half needs the `case` binding to alias
rather than copy the payload.
