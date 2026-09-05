# Seed interp: Option-wrapped extern bytes → misleading "unknown static method" from constructor overload scoring

- **Date:** 2026-07-20
- **Status:** open (seed Rust defect — .spl call-site workaround landed; see below)
- **Severity:** high (diagnostic actively misleads: reports a name-resolution
  failure for what is an argument-type mismatch; cost multiple debugging hours
  during the emit-object campaign)
- **Area:** src/compiler_rust/compiler/src/interpreter_method/special/objects.rs

## Symptom

`native-build --emit-object` (any target) dies at the very last step — after
llc has already produced a valid object file — with:

```
error: semantic: unknown static method object on class CodegenOutput
```

The method plainly exists (`codegen_types.spl:71`). The error is emitted at
RUNTIME (interpreter static-call dispatch), not during a semantic pass, and
fires only when the argument value fails overload scoring.

## Minimal repro (9 lines, seed `run`)

```simple
use compiler.backend.backend.codegen_types.{CodegenOutput}

extern fn rt_file_read_bytes(path: text) -> [u8]

fn main():
    val bytes = rt_file_read_bytes("any_existing_file")
    print "bytes-len {bytes.len()}"          # works — prints real length
    val o = CodegenOutput.object("x", bytes) # dies: "unknown static method object"
    print "probe4-ok {o.name}"
```

With a literal `[]` in place of `bytes`, the same call succeeds.

## Mechanism (source-confirmed)

1. `rt_file_read_bytes` (interpreter_extern/file_io.rs:407-416) returns
   `make_some(Value::array(...))` — an **Option-wrapped** array, per the
   general extern convention (cf. `rt_env_get(...) ?? ""` at every call site).
2. The `.spl` extern declaration says bare `[u8]`; method dispatch (`.len()`)
   sees through the wrapper, so the value looks healthy.
3. `handle_constructor_methods` (objects.rs:140) filters static-method
   candidates through `constructor_overload_score` (objects.rs:49).
   `constructor_value_matches_type` (objects.rs:~38-46) accepts
   Array/FrozenArray/Tuple for an array param and returns **false for
   `Value::Some(_)`** → score None → candidate dropped → the "unknown static
   method {m} on class {c}" branch fires (objects.rs:287) even though the
   method exists and only an argument failed to match.

## Expected (two independent fixes, both seed-side)

1. **Diagnostic honesty:** when candidates matching the NAME exist but all are
   rejected by overload scoring, report "no matching overload for static
   method `object` on class `CodegenOutput` (argument N: expected [u8], got
   Option<[i64]>)" — never "unknown static method".
2. **Scoring symmetry:** `constructor_value_matches_type` should unwrap
   `Value::Some(inner)` before matching (method dispatch and `??` already see
   through it; scoring is the odd one out).

## Workaround landed (.spl, root-cause-adjacent)

`src/compiler/70.backend/backend/llvm_backend_tools.spl` `compile_ir_to_object`
now unwraps the extern result before storing (`val byte_arr: [u8] = bytes ?? []`
after the nil guard), per the same convention every `rt_env_get` call site
already follows. Native builds return the bare array, so `?? []` is identity
there. Any OTHER call site that passes a raw `rt_*_bytes` result into a typed
static-method/constructor-overload parameter has the same latent failure —
audit before reusing this pattern.

## Context

Third layer of the emit-object onion
(`nvme_rv32_smp_flatten_seed_object_to_int_2026-07-19.md`): the
inline_functions crash (layer 1, fixed) masked this; fixing it exposed the
misleading error above, which cost a WC-archaeology detour before the
9-line repro isolated it. Note for future debugging: this error message can
mean "argument type mismatch", and earlier greens in a shared WC may have been
native-build **cache replays** (`[NATIVE] cache hit`) — always re-verify with
`SIMPLE_NATIVE_BUILD_CLEAN=1`.
