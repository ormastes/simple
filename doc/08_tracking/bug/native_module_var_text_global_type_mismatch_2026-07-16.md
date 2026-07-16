# Native: module-level `var s = ""` (text) global emits `global i64 <ptr>` → llc fails

**Severity:** P2
**Date:** 2026-07-16
**Area:** native codegen (module-level text/string global initialization)
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

## Root cause (hypothesis — verify)

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, the
module-mutable-globals loop (`for static_ in module.statics.values()` around
line 116):

```
val g_ty  = self.valid_llvm_type(self.llvm_type_text(static_.type_))   # -> "i64" for text
...
g_init = self.translate_const_value(init_const.value)                  # -> "getelementptr ... ptr"
self.builder.emit("{g_name} = global {g_ty} {g_init}")
```

For a `text` static the slot type resolves to `i64` (text is an i64 runtime
handle) but the constant initializer is a raw `ptr` (getelementptr into the
string byte array). The two disagree, so llc rejects the global. A text
module-global cannot be a compile-time-constant i64 handle; it needs either a
`ptrtoint`-wrapped initializer or a runtime `__init` sequence that boxes the
literal into the slot before first use.

## Impact

Any native binary with a module-level `var s = "..."` (or `= ""`) fails to
link. Workaround: hold text module state as an i64/enum flag, or initialize it
inside `main`/an init fn rather than at module scope.

## Verification note

Reproduced at commit `5c67273d180` (native-build loads there; at later commits
the seed cannot load current `src/compiler`). Not yet covered by
`scripts/check/check-native-seed-parity.shs` — adding a text-global case there
today would fail the harness until this is fixed.
