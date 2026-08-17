# Bootstrap LLVM IR buffer is never reset: every module after the first is emitted as (all previous modules ++ itself)

- **Date:** 2026-08-01
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Component:** `src/compiler/70.backend/backend/llvm_ir_builder.spl`
- **Severity:** High — pure-Simple LLVM backend emits IR that `llc` rejects for
  every module except the first one compiled in a process.

## Symptom

The pure-Simple LLVM backend emits a module whose header block appears twice
(or N times), which reads at a glance as a *corrupt / duplicated target
triple*:

```
; ModuleID = 'mod_a'
source_filename = "mod_a.spl"
target datalayout = "e-m:e-p270:32:32-..."
target triple = "x86_64-unknown-linux-gnu"

define i64 @mod_a() nounwind {
  ret i64 42
}

; ModuleID = 'mod_b'          <-- second module's header, mid-file
source_filename = "mod_b.spl"
target datalayout = "e-m:e-p270:32:32-..."
target triple = "x86_64-unknown-linux-gnu"

define i64 @mod_b() nounwind {
  ret i64 42
}
```

`llc-18` rejects it at the **second** header line:

```
llc-18: error: modb.ll:11:1: error: expected top-level entity
source_filename = "mod_b.spl"
^
```

(`LLC_RC=1`.)

## Root cause

`LlvmIRBuilder` accumulates IR text in the per-instance `sb` field (an
`rt_string_builder` handle). But under `SIMPLE_BOOTSTRAP=1`, `emit()` takes a
completely different path and appends to the **module-level global**
`_llvm_bootstrap_ir_text` instead:

```
me emit(line: text):
    if (rt_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1":
        val current = _llvm_bootstrap_ir_text ?? ""
        if current == "":
            _llvm_bootstrap_ir_text = line
        else:
            _llvm_bootstrap_ir_text = "{current}\n{line}"
        return
    ...
```

and `build()` / `llvm_ir_builder_build()` return that global in preference to
the instance buffer:

```
me build() -> text:
    val bootstrap_ir = _llvm_bootstrap_ir_text ?? ""
    if bootstrap_ir != "":
        return bootstrap_ir
    rt_string_builder_finish(self.sb)
```

That global is the mirror of the per-instance `sb`, but unlike `sb` — which is
freshly allocated by `rt_string_builder_new()` in `LlvmIRBuilder.create()` —
**it was never reset**. So a second builder in the same process kept appending
to the first builder's text, and `build()` handed back the concatenation.

The two construction sites are `MirToLlvm.create` and
`MirToLlvm.create_baremetal` (`_MirToLlvm/class_def.spl:142,178`), one builder
per `MirToLlvm`, one `MirToLlvm` per module. So "new builder" == "new module",
and the reset belongs exactly where `sb` is allocated.

## Fix

Clear the global in `LlvmIRBuilder.create()`, symmetric with the fresh
`rt_string_builder_new()` allocated on the same line:

```
static fn create(name: text, target: LlvmTargetTriple) -> LlvmIRBuilder:
    val st = if target.is_32bit(): "i32" else: "i64"
    _llvm_bootstrap_ir_text = ""
    LlvmIRBuilder(...)
```

Bare-metal attributes are *not* affected: `emit_baremetal_attributes()` queues
into the per-instance `pending_baremetal_attrs` list and is called *after*
`create()` returns, so clearing in `create()` cannot drop them.

## Evidence

Harness (two modules built from one process, `SIMPLE_BOOTSTRAP=1`):

- **Before:** `=== MODULE B ===` output contained the whole of module A ahead of
  module B — two `ModuleID`, two `source_filename`, two `target datalayout`,
  two `target triple`. `llc-18 -filetype=obj` → `expected top-level entity`,
  rc=1.
- **After:** module B is standalone, one header. `llc-18 -filetype=obj` → rc=0,
  object produced, `nm` shows `0000000000000000 T mod_b` (positive artifact,
  not merely a zero exit).

## Regression test

`test/unit/compiler/backend/llvm_ir_builder_spec.spl` —
"LLVM IR Builder bootstrap buffer isolation" / "does not prepend a previous
module's IR to the next module". It sets `SIMPLE_BOOTSTRAP=1` via `rt_env_set`,
builds two modules, and asserts module B contains no trace of `mod_a` and has
exactly one `target triple` / `source_filename`.

Non-vacuity (RED before GREEN), same binary and tree:

- fix reverted → `Results: 4 total, 0 passed, 4 failed` (new test among them)
- fix applied  → `Results: 4 total, 1 passed, 3 failed` (new test GREEN)

The 3 remaining failures are **pre-existing and unrelated**: the older cases in
that spec assert on a `builder.instructions` field that no longer exists on the
class (it was replaced by the `sb` string-builder handle). They fail identically
with and without this change. Not touched here.

## Notes / non-findings

- `LlvmTargetTriple.to_text()` was **cleared** as a cause. A standalone probe of
  its nullable/Option `match self.env: Some(env) / nil` returned
  `x86_64-unknown-linux-gnu` and `x86_64-unknown-simpleos` correctly under the
  JIT. The duplicated-header effect above fully explains the "corrupt target
  triple" symptom.
- Constant emission is **correct at this layer**: the harness emitted
  `ret i64 42` faithfully. The separate "every function comes out `ret i64 0`"
  defect is therefore *not* in `LlvmIRBuilder`; it lives upstream in
  MIR→LLVM translation and remains open.
