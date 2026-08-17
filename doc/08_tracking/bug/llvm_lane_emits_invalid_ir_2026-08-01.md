# Pure-Simple LLVM lane emits invalid IR for every program

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  defects 3 and 4 remain open
- **Owner:** Codex `/root/symbolid_zero_spec/simpleos_unoq_stage3`
- **Claim scope:** stop retaining the target composite, reconstruct a fresh
  header target from the scalar requested target, and compose triple text
  inline in `emit_module_header`; cover GNU, nil-env and SimpleOS neighbors
  without changing the Rust runtime.
- **Date:** 2026-08-01
- **Base:** `63c362526c2b01c5bc63697ab80aea1501ae65fe` (the
  `llvm_ir_builder.spl` blob is byte-identical at `205b35e474a`, where the
  defects were first isolated, and at this tip: `91d262b9e29`)
- **Lane:** the pure-Simple `CompilerDriver`, reached with a **bare positional**
  `.spl` (`simple native-build foo.spl -o foo.out`), which
  `src/app/cli/bootstrap_main.spl:239-285` routes in-process. NOT
  `native-build --entry`, which `:225-228` delegates to the `rt_native_build`
  Rust seed.
- **Stage2 under test:** built from this base with the seed
  (`728 compiled, 0 cached, 0 failed` — the expected baseline).

## Headline

The failure is **not enum-specific and not match-specific**. A six-line program
with no enum, no match and no pattern binding already produces rejected IR.
No enum-value assertion can pass on this lane until these are fixed.

## Reproduction and captured IR

`c1.spl`:

```
fn f() -> i64:
    return 100

fn main() -> i64:
    print "f={f()}"
    return 0
```

`TMPDIR=... simple native-build c1.spl -o c1.out` → exit 1,
`error: in-process native-build: AOT compile error in c1: <invalid-heap:0x2491ae11>`.

The emitted `.ll` (`$TMPDIR/simple_llvm_<pid>.ll`, written by
`src/compiler/70.backend/backend/llvm_backend_tools.spl:130`) contains:

```
target triple = "<invalid-heap:0x2491ae11>"
...
define i64 @__simple_main() nounwind readonly alwaysinline {
bb0:
  ret i64 0
}

define i64 @f() nounwind readonly alwaysinline {
bb0:
  ret i64 0
}

; TBAA metadata
!100 = !false
!101 = !{!"int", !{base}, i64 0}
!106 = !{!{base + 1}, !{base + 1}, i64 0}
```

## Four distinct defects, isolated by bisecting the IR text

`llc` was run against the captured IR with each defect repaired in turn:

| Repair applied | `llc` result |
|---|---|
| none | `error: unable to get target for '<invalid-heap:0x25d641f1>'` |
| triple only | `error: t_triple.ll:69:8: expected metadata type` at `!100 = !false` |
| triple + TBAA block removed | **exit 0** |

### 1. Invalid TBAA metadata — FIXED

`llvm_ir_builder.spl:537` `emit_tbaa_hierarchy()` emitted
`"!{base} = !{!\"Simple TBAA\"}"`. A bare `{` inside a text literal opens a
string interpolation, so `{!"Simple TBAA"}` was evaluated as the expression
`!"Simple TBAA"` and rendered `!false`. The sibling lines degraded the other way
and emitted the un-substituted text `!{base}` verbatim.

The body was supposed to be switched off by a bare `return` above it, but a
**statement-level `return` does not terminate the function on the compiled
lanes** — see `top_level_return_falls_through_2026-08-01.md`. So it ran on every
module. There was never a "disabled" state in practice: the choice was between
emitting broken metadata always and emitting valid metadata always.

Fixed by sourcing the literal braces from `lb`/`rb` locals, which makes the
metadata verifier-clean and keeps
`test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl`'s "Simple TBAA"
expectation honest instead of green-by-accident. The fix does not depend on the
broken `return` guard working.

#### Verification of the fix (independent re-run)

| Check | Result |
|---|---|
| patched emit lines, run standalone | `!100 = !{!"Simple TBAA"}`, `!101 = !{!"int", !100, i64 0}`, `!106 = !{!101, !101, i64 0}` |
| pristine emit lines, run standalone | `!100 = !false`, `!101 = !{!"int", !{base}, i64 0}` |
| `llc-18` on captured IR, pristine TBAA | exit 1 — `t_triple.ll:69:8: error: expected metadata type` at `!100 = !false` |
| `llc-18` on the same IR with the patched TBAA block | **exit 0**, `.s` emitted |
| stage2 self-build, pristine | `728 compiled, 0 cached, 0 failed` |
| stage2 self-build, patched | `728 compiled, 0 cached, 0 failed` |
| patched **stage2 binary** on `c1.spl`, emitted `.ll` | `!100 = !{!"Simple TBAA"}` (was `!100 = !false`) |

`c1.spl` still fails to build on both binaries with the identical
`<invalid-heap:0x...>` error, because defect 2 below is untouched. Defect 1 is
fixed and does not regress anything; it is not on its own sufficient to make the
lane work.

### 2. `target triple` is a corrupt heap value — FIXED

`llvm_ir_builder.spl:99` emits `target triple = "{self.target.to_text()}"` and
gets `<invalid-heap:0x...>`, the runtime's marker (`src/compiler_rust/runtime/
src/value/sffi/io_print.rs:474`) for a Value whose raw is not a valid heap
pointer. An isolated re-implementation of `LlvmTargetTriple.to_text()`'s exact
shape (struct with `text` fields plus a `text?` matched via `Some(e)`/`nil`)
compiled by the same seed prints `x86_64-unknown-linux-gnu` correctly, so the
corruption is in `self.target` reaching `emit_module_header`, not in `to_text()`
itself. Not yet located.

The first proposed repair snapshotted `target.to_text()` inside
`LlvmIRBuilder.create()`. A rebuilt 725/725 diagnostic Stage 3 rejected that
approach: the resulting pure-Simple shard still emitted
`target triple = "<invalid-heap:...>"`. The incoming composite is therefore
already unsafe at that boundary; moving the same conversion earlier is not a
fix.

Reconstructing a fresh local, the shape previously used by `6087e7a9d83`, was
also falsified by a second rebuilt 725/725 diagnostic Stage 3: calling
`target.to_text()` on that local still emitted `<invalid-heap:...>`. The defect
is the newly interpolated text crossing the compiled `to_text()` method return
boundary, not only composite retention.

The current source candidate keeps the useful part of that repair:
`LlvmIRBuilder` no longer stores the composite target, and
`emit_module_header()` reconstructs a fresh local `LlvmTargetTriple` from the
scalar `SIMPLE_NATIVE_BUILD_TARGET`. The selector covers hosted x86-64,
AArch64, RISC-V 64/32, x86, ARM, Wasm 64/32 and SimpleOS; bare-metal target
strings use `from_target_baremetal`. Header emission calls `datalayout()` (which
returns stable literals), but composes arch/vendor/os/optional-env directly in
the caller and never calls `to_text()`.

Focused regression evidence:

- pre-fix Rust-seed interpreter diagnostic: 2/4 passed, with the structural
  retained-composite assertion red;
- repaired Rust-seed interpreter diagnostic: 4/4 passed for exact GNU x86-64,
  nil-env AArch64 bare metal, SimpleOS, and no retained builder composite;
- final pure-Simple proof: diagnostic Stage 3 rebuilt 725/725, compiled the
  exact `env/paths` shard through the repaired builder, and emitted
  `target triple = "x86_64-unknown-linux-gnu"` with no `<invalid-heap:` value;
- `llc` consumed that header and advanced to the independent invalid
  `%t281 = bitcast i1 %l162 to ptr` error at generated IR line 2874. That
  progression is the compiled-native proof that defect 2 is closed, not a
  claim that the full shard or Stage 4 now passes.

### 3. Constants are lost — every `ret` is `ret i64 0` — OPEN

`f()` must `ret i64 100`; it emits `ret i64 0`, and no `add i64 100, 0
; const int` line is emitted at all. `translate_const`
(`_MirToLlvm/core_codegen.spl:923`) appears never to run for it. The `ret 0`
text itself comes from the fallback at `core_codegen.spl:821-822`.

The same shape appears for `match`: an integer `match` (no enums) emits
`inttoptr i64 undef to ptr` and `icmp ne i64 undef, 0` — every operand `undef`,
every arm `ret i64 0`.

This is the mechanism behind the reported "`rt_enum_new` receives payload 0" and
"`-O3` folds affected bodies to `ret 0`": the payload constant never reaches the
IR in the first place, so `-O3` is folding correct IR over a value that was
already zero.

**A second tempting theory was refuted:** that defects 2 and 3 are themselves
downstream of the statement-level `return` miscompile — stage2 is built by the
seed, so any compiler source with a dead statement-level `return` guard would
misbehave inside stage2. A sweep of every `.spl` under `src/compiler/` for "a
`return` whose next non-blank non-comment line has the same indentation" returned
9 hits, 7 of them docstring prose. The only two real sites are
`llvm_ir_builder.spl:545` and `effect_pass.spl:27` — **neither is on the
`translate_const` or `LlvmTargetTriple.to_text()` path**. So the `return` defect
does not explain defects 2 and 3. Do not re-run that theory.

**A tempting theory was refuted:** `translate_terminator`'s
`case Copy(local) | Move(local)` arm mis-matching a `Const` operand. A direct
probe of an or-pattern-with-binding against a non-matching variant, compiled by
the same seed codegen (lane proved via `rt_enum_check_discriminant`), returned
the correct answer (`999`, not `111`). Do not re-run that theory without new
evidence.

### 4. `add void <int>, 0` — NOT REPRODUCED at this base

The reported `add void 7, 0` was not reproduced here; this base loses the
constant entirely instead. The site that would emit it is
`_MirToLlvm/core_codegen.spl:940`, `add {llvm_ty} {v}, 0  ; const int`, with
`llvm_ty` = `"void"` from `llvm_type_text`'s `MirTypeKind.Unit | Never` arm
(`_MirToLlvm/class_def.spl:128`). Note the `Zero` const arm at `:972` already
guards `llvm_ty == "void"` while the `Int`/`Float`/`Bool` arms do not, and
`valid_llvm_type` (`:1579`) filters only `""`/`"nil"`, not `"void"`. That is the
type-mapping site to fix if the shape resurfaces.

## Other observations from the same session

- `simple native-build ret2.spl -o out` (a bare `return` followed by a `print`)
  **segfaults** the pure-Simple lane.
- `enum` construction in the single-file lane fails resolution:
  `[mir-lower] WARNING: unresolved method call 'I' lowered to const-0
  placeholder (silent-null risk, Task #145)` then
  `MIR lowering error: unresolved method call: I` for `E.I(7)`.
