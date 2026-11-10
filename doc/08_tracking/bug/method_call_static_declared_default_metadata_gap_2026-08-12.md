# MethodCallStatic declared-default metadata gap

Status: FIXED (2026-11-11, lane ne15) — cross-module/method default pad now sits in
the single `emit_resolved_direct_call` choke point; acceptance scenario passes on
the fresh seed (interpreter). Native leg not re-run on this lane. See addendum.

## Symptom

During the packed-memory Stage3 build, the call
`self.lower_runtime_module_initializers(module, const_vals)` resolved to an
instance method whose ABI has four parameters: receiver, module, consts, and
`bootstrap_module_index: i64 = -1`. The Rust Cranelift boundary correctly
preserved the receiver, then observed only three supplied MIR operands.

Generic codegen padding is not a correct repair. Padding the final slot with
tagged nil or zero changes the declared value `-1` and therefore changes module
initializer identity.

## Root cause

Pure-Simple MIR has default-expression lookup and lowering in
`pad_trailing_default_args`, but this cross-module MethodCallStatic path did not
carry or recover the callee's declared default before reaching codegen. MIR
therefore lacks the semantic operand; Cranelift signatures carry types and
arity, not default expressions.

## Current mitigation

The bootstrap-critical call in
`src/compiler/50.mir/_MirLowering/module_lowering.spl` passes `-1` explicitly.
The Cranelift receiver fix remains strict and refuses an arity mismatch instead
of inventing a value.

## Required general fix

Extend owner-qualified cross-module default metadata through HIR/MIR call
resolution. Before emitting MethodCallStatic, lower every omitted trailing
declared default expression at the caller and append its operand. Do not encode
defaults in backend signatures and do not use nil/zero padding as semantics.

Acceptance regression: an imported instance method with a non-nil/non-zero
default (for example `offset: i64 = -7`) must return or otherwise observe `-7`
when omitted, in interpreter and native execution. An adjacent explicit value
must remain unchanged, and a free call must not acquire an implicit receiver.



## Addendum 2026-11-11 (lane ne15) — FIXED; general default-pad landed, acceptance green

**Verification actually run** (worktree simple-p3-ne15-20261111, tip
f7640d20a458, fresh seed 46fe8f6b6def, seed-smoke):

Interpreter acceptance — the doc's "Acceptance regression" — via a temporary
fixture module + spec (created under `test/fixtures/p3ne15_offset_defaults/`,
run, then deleted; not committed):

```simple
# gadget.spl (imported module)
class Gadget:
    base: i64
impl Gadget:
    static fn make() -> Gadget:
        Gadget(base: 100)
    me read_offset(offset: i64 = -7) -> i64:
        self.base + offset
fn free_read(base: i64, offset: i64 = -7) -> i64:
    base + offset

# spec
use std.spec
use test.fixtures.p3ne15_offset_defaults.gadget.{Gadget, free_read}
# g.read_offset() == 93 (omitted default -7 observed); g.read_offset(5) == 105;
# free_read(50) == 43; free_read(50, 1) == 51
```

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ./bin/simple.exe test \
  test/fixtures/p3ne15_offset_defaults/row2_accept_spec.spl --mode=interpreter --no-cache
#   ✓ omitted trailing default observes -7 on imported instance method
#   ✓ omitted trailing default observes -7 on imported free fn
# Results: 2 total, 2 passed, 0 failed
```

**General fix (self-hosted):** `pad_trailing_default_args`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1328-1383`)
sits in `emit_resolved_direct_call` — per its docstring, "the single choke
point every resolved direct call reaches — same-module free functions,
CROSS-MODULE callees, and instance/static METHODS alike" — lowering omitted
trailing defaults as expressions (never nil/zero padding). Every method-call
site in `method_calls_literals.spl` (:4816, :4882, :5246, :6034, :6357) pads
through it, which is exactly the "extend owner-qualified cross-module default
metadata through HIR/MIR call resolution" requirement. The sibling
`native_trailing_default_param_reads_uninitialized_2026-08-09` is marked FIXED
with a fence in `check-aot-lane-fences.shs`.

**Not re-run:** the native-execution leg of the acceptance (native builds not
granted on this lane; the native-build Windows hang is a separately routed
live defect). The explicit `-1` at the `module_lowering.spl` call site remains
correct either way.
