# Native: module-level `var s = ""` (text) global emits `global i64 <ptr>` → llc fails

**Severity:** P2
**Date:** 2026-07-16
**Area:** native codegen (module-level text/string global initialization)
**Status:** runtime-initializer candidate under review; execution pending
**Related:** `native_module_var_bool_garbage_init_2026-06-13.md` (bool/i64 scalar
globals — RESOLVED; this is the text sub-case that fix does not cover)

## Repro

```simple
var NAME = ""

fn main():
    print "name=[{NAME}]"
```

`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry m.spl -o m --clean`:

```
error: AOT compile error in m: CompileError(message: llc failed (exit 1):
/usr/bin/llc-18: /tmp/simple_llvm_*.ll:47:22: error: constant expression type
mismatch: got type 'ptr' but expected 'i64'
@g_NAME = global i64 getelementptr inbounds ([1 x i8], ptr @.str.0, i64 0, i64 0)
                     ^
```

Bool and i64 module globals in the same program compile and run correctly
(see the related bug doc). Only a text/string module-global triggers this.

## Root cause and source fix

The unannotated module binding was assigned `HirTypeKind.Infer`; MIR has no
`Infer` lowering arm, so it fell back to `i64`. The shared HIR `lower_const`
owner now infers primitive literal bindings as `i64`, `f64`, `text`, or `bool`.
The existing MIR and LLVM type mapping then emits the string slot as `ptr` and
keeps its raw literal relocation unchanged. A parse-to-LLVM regression covers
all four primitive literal branches and rejects `global i64 getelementptr`.

Do not use `ptrtoint`: it would only silence llc while leaving downstream reads
typed as integers. Cranelift still fails closed here. Its string constants and
later `StoreGlobal` values are boxed/tagged through `rt_string_new`; initializing
the same slot with a raw rodata pointer would silently change representation
after the first assignment. The existing rodata also carries neither a trailing
NUL nor a stored length, so it cannot safely initialize the original empty-text
case. Cranelift needs one consistent init/load/store representation, including
its text-cast path, before a relocation or runtime initializer is accepted.

## Original emitter symptom

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, the
module-mutable-globals loop (`for static_ in module.statics.values()` around
line 116):

```
val g_ty  = self.valid_llvm_type(self.llvm_type_text(static_.type_))   # -> "i64" for text
...
g_init = self.translate_const_value(init_const.value)                  # -> "getelementptr ... ptr"
self.builder.emit("{g_name} = global {g_ty} {g_init}")
```

At the failing revision the upstream `Infer` fallback supplied `i64` as the
static type while the string constant correctly supplied a raw pointer. The
emitter therefore combined two inconsistent inputs; the fix belongs at HIR
type inference, not in this emission loop.

## Pre-fix impact

Default-LLVM native binaries with an unannotated module-level `var s = "..."`
(or `= ""`) failed to compile. Explicit Cranelift remains unsupported for this
shape until its text-global runtime representation is implemented consistently.

## Verification note

Reproduced at commit `5c67273d180` (native-build loads there; at later commits
the seed cannot load current `src/compiler`). The source regression is present;
execution is pending a valid pure-Simple runner. Higher-level review rejected a
raw-pointer relocation because it disagrees with boxed stores and masks the
empty-string length/NUL requirements. A strict dual-backend parity case must
cover initial read, reassignment, and a real text operation in both JIT and AOT.

## 2026-07-25 bootstrap blocker

The candidate now lowers non-foldable module globals into one ordered
`__module_init_*` function and has a strict LLVM/Cranelift fixture for derived
`text`, module `[text]`, indexing, mutation, and persistence. It is not safe to
execute yet: the bootstrap real-LLVM path emits functions from a flat
cross-module accumulator, but does not carry the matching `MirStatic`
declarations. Emitting the initializer alone would therefore target undeclared
globals; merging statics naively can also collide on module-local `SymbolId`
values.

Acceptance requires carrying or remapping each module's statics with its flat
functions, then running the focused parity case once on both backends. No full
bootstrap should run before that focused case passes.

The bootstrap candidate now carries module-owned statics with stable remapped
IDs, emits them before flat functions, and calls one dependency-ordered
`__module_init_all`. Focused source checks pass. Runtime parity has not run:
the first sparse-worktree attempt stopped before compilation because
`bin/simple` was absent, and the deployed test runner independently resolves
its delegate as `/usr/bin/simple_seed`. Imported globals remain outside this
fix; the regression covers globals owned and used by their defining module.

A guarded self-hosted candidate build on 2026-07-25 also stopped before
artifact creation: the deployed CLI rejected `--low-memory`, then the single
corrected LLVM attempt exited with SIGSEGV 139 after five seconds. Both output
and cache directories stayed empty. Per the three-cycle/runaway guard, do not
retry or start a full bootstrap in this lane; resume from a separately admitted
self-hosted candidate and run only
`NATIVE_PARITY_CASES=module_global_text_array_persistence`.
