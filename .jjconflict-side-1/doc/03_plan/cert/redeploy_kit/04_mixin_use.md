# Redeploy Kit 04 — mixin `use` on class (garbage) and struct (not wired)

Covers two related repros:
- `test/cert/redeploy_pending/mixin_class_use.spl`
- `test/cert/redeploy_pending/mixin_struct_use.spl`

## Defect
```
mixin Scorable:
    score: i64
    fn add_score(n: i64) -> i64: return self.score + n

class Player:  use Scorable   name: text     # class case
struct Player: use Scorable   name: text     # struct case
```
- class case (memory-safety, critical): `p.add_score(5)` prints a raw
  `<value:0x...>` heap tag, `p.name` prints `0.0`. Expected `15` / `Alice`.
- struct case (high): stderr `Runtime error: Function 'Player.add_score' not
  found`; stdout leaks a fabricated `error` then `0`; process still exits 0.

## Root cause (analysis — not yet fixed)
Two distinct layers fail:

1. `struct X: use Mixin` — mixin injection is implemented for the `class` path
   only. In `src/compiler_rust/compiler/src/interpreter_eval.rs` the mixin
   field/method injection (`// Inject mixin fields and methods into class`,
   ~line 637) runs on class definitions; the struct definition path has no
   equivalent, so `add_score` is never registered for the struct → "Function
   not found" at call time. The call result then degrades to the SPECIAL_ERROR
   value, which `print` renders as the literal `error` — a TOR-FM-02 silent-bad
   -output hole (exit 0 with fabricated stdout).

2. `class X: use Mixin` — injection exists at the semantic level but the JIT
   codegen for the mixin-injected FIELD LAYOUT and method receiver is wrong:
   `self.score` reads the wrong offset (mixin-injected field not placed in the
   struct layout the codegen computes), so `add_score` returns an
   unboxed/garbage value (`<value:0x...>`) and `p.name` reads `0.0` (field
   offsets shifted by the un-accounted injected `score` field).

## Fix direction (requires seed rebuild to verify)
- Apply mixin field/method injection uniformly to BOTH `class` and `struct`
  definitions (single shared injection pass over the composed type), OR reject
  `struct X: use Mixin` at compile time with a clear diagnostic if struct mixins
  are intentionally unsupported. Silent accept + fabricated `error` on stdout is
  the unacceptable state.
- Ensure the injected mixin fields participate in the SAME struct layout /
  field-offset computation the codegen uses, so injected-field reads/writes and
  subsequent named-field offsets are correct, and method results are boxed per
  their declared return type.
- A "Function not found" at runtime must set a non-zero exit code, never leak a
  fabricated value to stdout while exiting 0.

## Test plan
- Both specs expect `15` then `Alice`, exit 0 (or, for struct, a compile-time
  rejection — but never the fabricated-`error` silent-accept state).

## Verify-now vs redeploy-pending
- REDEPLOY-PENDING + NOT-YET-FIXED: root cause split across mixin injection
  (struct path missing) and JIT field-layout codegen (class path); fixes live in
  the frozen seed and are not implemented/verified this session.
