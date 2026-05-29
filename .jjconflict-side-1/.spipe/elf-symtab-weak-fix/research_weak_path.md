# ELF SYMTAB Weak Binding — Research Brief

## Q1: MIR Representation of "Weak"

`MirFunction` has **no `is_weak` or `linkage` field**. The struct
(`src/compiler_rust/compiler/src/mir/function.rs:73`) carries:

```
pub name: String
pub params / locals / blocks / ...
pub visibility: Visibility
pub attributes: Vec<String>   // e.g. ["inject", "test"]
pub effects: Vec<String>
pub layout_phase: LayoutPhase
pub is_event_loop_anchor: bool
pub is_generic_template: bool
...
```

There is no `is_weak`, `linkage`, or `boot_alias` field anywhere on
`MirFunction` or `MirModule`.

`MirModule` (`mir/function.rs:~315`) does have:
- `local_globals: HashSet<String>` — used by codegen to choose
  `Import` vs `Preemptible` linkage for *globals*, not functions.
- No per-function weak flag.

**Gap:** The pipeline has no way to express "this function should emit
as a weak ELF symbol." To fix the bug, a `is_weak: bool` field (or a
richer `linkage: MirLinkage` enum) must be added to `MirFunction`.

---

## Q2: AST/HIR Weak Annotation

There is **no `@weak` annotation or `weak` keyword** in the Simple
language that flows through AST → HIR → MIR for functions. Grepping
`src/compiler_rust/compiler/src/` (excluding `/mir/`) for `is_weak`,
`@weak`, `boot_alias`, `WeakLink` finds nothing in the HIR or AST
layers.

The only `weak` references in HIR/AST territory are:
- `PointerKind::Weak` — reference-counted weak pointers (unrelated).
- `MirInst::WeakDecrement` — RC decrement (unrelated).
- `cranelift.rs:306` — object-copy utility passthrough of `symbol.is_weak()` for Mach-O relinking.

The LLVM backend (`codegen/llvm/backend_core.rs:406,420,427`) uses
`inkwell::module::Linkage::WeakAny` for all functions-with-bodies but
this is a blanket rule for duplicate-symbol avoidance, not a per-function
weak annotation flowing from the AST.

---

## Q3: cranelift-object Linkage → ELF SymbolBinding Mapping

**Key function** in
`src/compiler_rust/vendor/cranelift-object/src/backend.rs:886`:

```rust
fn translate_linkage(linkage: Linkage) -> (SymbolScope, bool) {
    let scope = match linkage {
        Linkage::Import      => SymbolScope::Unknown,
        Linkage::Local       => SymbolScope::Compilation,
        Linkage::Hidden      => SymbolScope::Linkage,
        Linkage::Export
        | Linkage::Preemptible => SymbolScope::Dynamic,
    };
    let weak = linkage == Linkage::Preemptible;
    (scope, weak)
}
```

This `weak` bool feeds `write::Symbol { weak, scope, ... }`, and the
object-crate ELF writer
(`vendor/object-0.36.7/src/write/elf/object.rs:669`) translates it:

```rust
let st_bind = if symbol.weak {
    elf::STB_WEAK         // 2
} else if symbol.is_undefined() {
    elf::STB_GLOBAL       // 1
} else if symbol.is_local() {
    elf::STB_LOCAL        // 0
} else {
    elf::STB_GLOBAL       // 1
};
```

**Therefore:**
- `Linkage::Preemptible` → `scope=Dynamic, weak=true` → **STB_WEAK** (correct for boot-alias stubs that should be overridable)
- `Linkage::Local`       → `scope=Compilation, weak=false` → **STB_LOCAL**
- `Linkage::Export`      → `scope=Dynamic, weak=false` → **STB_GLOBAL**

The ELF `sh_info` invariant (all LOCAL symbols must appear before the
first non-LOCAL in SYMTAB, and `sh_info` = index of first non-LOCAL)
is violated if a symbol that *should* be `STB_WEAK` (non-LOCAL) is
instead emitted as `STB_LOCAL`.

---

## Q4: The declare_functions Gap and Where to Add Weak

**Location:** `src/compiler_rust/compiler/src/codegen/common_backend.rs:526–555`

```rust
let (symbol_name, linkage) = if func.name == "main" && has_body {
    if self.is_entry_module {
        ("spl_main".to_string(), cranelift_module::Linkage::Preemptible)
    } else {
        (self.mangle_name(&func.name), cranelift_module::Linkage::Local)
    }
} else if !has_body {
    (self.sanitize_symbol(&func.name), cranelift_module::Linkage::Import)
} else {
    // ALL functions with bodies → Preemptible
    (self.mangle_name(&func.name), cranelift_module::Linkage::Preemptible)
};
```

The **non-entry-module `main`** arm produces `Linkage::Local`
→ `STB_LOCAL`. If the intent is a *weak boot-alias* symbol (e.g.,
`_start` or a renamed entry that boot code can override), `Local` is
wrong; it should be `Linkage::Preemptible` → `STB_WEAK`.

The freestanding boot-alias path
(`pipeline/native_project/linker.rs:1127–1174`) currently works around
this via linker `--defsym` flags (`freestanding_weak_boot_defsyms`),
not by emitting correct weak ELF symbols from codegen.

### Required Fix (two-part)

**Part A — Add `is_weak` to `MirFunction`**
File: `src/compiler_rust/compiler/src/mir/function.rs`
Add field: `pub is_weak: bool` (default `false`) to `MirFunction`.
Initialize to `false` in `MirFunction::new`.
Set it to `true` in `mir/lower/lowering_core.rs` (around line 591,
where linkage decisions are made) for functions that carry a `weak`
attribute or are boot-alias candidates.

**Part B — Use `is_weak` in `declare_functions`**
File: `src/compiler_rust/compiler/src/codegen/common_backend.rs`
In the `else` branch (line 546–550), check `func.is_weak` before
defaulting to `Preemptible`:

```rust
} else {
    let lnk = if func.is_weak {
        cranelift_module::Linkage::Preemptible  // → STB_WEAK (correct)
    } else {
        cranelift_module::Linkage::Preemptible  // already correct for normal fns
    };
    (self.mangle_name(&func.name), lnk)
}
```

Also fix the non-entry `main` arm: if the non-entry main is intended
as a weak boot alias, change `Linkage::Local` → `Linkage::Preemptible`
(line 541).

**Part C — Optional: `Linkage::Export` for non-overridable entry**
If `spl_main` should be a *strong* global (not overridable), use
`Linkage::Export` (→ `STB_GLOBAL`) instead of `Preemptible`
(→ `STB_WEAK`) for the entry-module main at line 539. Currently
`spl_main` is emitted as `STB_WEAK`, meaning a strong `spl_main`
anywhere else will silently win. This may or may not be intentional.

---

## File / Line Summary

| What | File | Lines |
|------|------|-------|
| `MirFunction` struct (no `is_weak`) | `src/compiler_rust/compiler/src/mir/function.rs` | 73–117 |
| `declare_functions` linkage decision | `src/compiler_rust/compiler/src/codegen/common_backend.rs` | 526–555 |
| `translate_linkage` (cranelift→object) | `src/compiler_rust/vendor/cranelift-object/src/backend.rs` | 886–895 |
| ELF `st_bind` from `symbol.weak` | `src/compiler_rust/vendor/object-0.36.7/src/write/elf/object.rs` | 669–676 |
| `write::Symbol.weak` field | `src/compiler_rust/vendor/object-0.36.7/src/write/mod.rs` | 913 |
| Freestanding boot-alias `--defsym` workaround | `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` | 1127–1174 |
| `is_optional_weak_hook_symbol` | `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` | 43–55 |
| LLVM `WeakAny` linkage (parallel backend) | `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` | 406–427 |
| Cranelift `Linkage` enum | `src/compiler_rust/vendor/cranelift-module/src/module.rs` | 138–188 |
