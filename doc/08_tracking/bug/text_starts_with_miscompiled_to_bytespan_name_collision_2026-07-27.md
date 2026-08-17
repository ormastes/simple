# `text.starts_with()` miscompiled into `ByteSpan.starts_with` — cranelift codegen resolves methods by NAME ONLY

- **ID:** text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27
- **Date:** 2026-07-27 (root cause corrected 2026-07-27, see *Correction*)
- **Area:** `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
  (:676-684) — the cross-module `use_map` suffix-scan arm of
  `compile_method_call_static`
- **Severity:** high — silent miscompile to an unrelated function, then a page
  fault on garbage. 28 known call sites across the CSS path.
- **Status:** OPEN, **fix IN FLIGHT.** Root cause **PROVEN** (five independent
  proof steps, below). Repro reduced to **0.5s**.
- **Class:** flat-registry name collision — same family as the known
  `interp env_get` defect (cross-linked below), now for METHODS.

## Correction — the previously recorded location was WRONG (retracted, not deleted)

> **RETRACTED:** earlier revisions of this doc named
> `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:604-639` and
> `:1520` as the defect site, and described the fix as widening an
> "in-tree guard" there. **That is wrong. Do not patch there.**
>
> This retraction is kept deliberately. **Two separate sessions already burned
> themselves patching that Simple file** — each built a FULL compiler and
> observed **zero effect on all five test cases**. Deleting the wrong location
> silently would invite a third session to repeat it.
>
> `method_calls_literals.spl` never participates in this decision. The real
> defect is in **Rust**, in `compiler_rust`, downstream of MIR.

## Symptom

Whenever `common.bytes.span` is anywhere in the entry closure, a
`text.starts_with(...)` call whose **receiver type was lost** (e.g. the result
of `.lower()`) binds to **`ByteSpan.starts_with`** — an unrelated struct's
same-named method. The wrong callee reads the receiver as a `ByteSpan` and
dereferences garbage.

Method resolution in this codegen arm happens **by name only**. Nothing checks
that the receiver is actually a `ByteSpan`.

Guest symptom: page fault, `cr2=0x0000001700000008`.

> **Read that cr2 carefully.** The `0x17` is an
> `RtCoreArray.transient_scope_id` being read at the ByteSpan `data` field
> offset — it is **NOT a length**, which is exactly what it looks like at a
> glance. Misreading it as a length sends you hunting an array-bounds bug that
> does not exist.

## Smoking gun

`src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl:29` — two calls on
**adjacent lines**, one miscompiled and one correct:

```
    if lower.starts_with("hsla(") and cleaned.ends_with(")"):
```

| call | receiver | emits |
|---|---|---|
| `lower.starts_with("hsla(")` | result of `.lower()` — type lost | `common__bytes__span__ByteSpan_dot_starts_with` ❌ |
| `cleaned.ends_with(")")` (same line) | typed `text` | `rt_string_ends_with` ✅ |

`rt_string_starts_with` exists and is used correctly in 86 other places. So
this is not a missing runtime function — it is resolution picking the wrong
one when, and only when, the receiver type is unavailable.

## Blast radius

**28 affected call sites across the CSS path**, including `apply_decls`,
`attr_selector_matches`, `extract_css_vw`, `parse_color_value`,
`_wm_window_gradient_from_css`.

Scope is broader in principle: any `text` predicate method (`starts_with`,
`ends_with`, `contains`) on a type-erased receiver, in any entry closure that
happens to include a struct declaring a same-named method. The CSS path is
merely where a `ByteSpan` import and `.lower()` results coincide.

## Proven root cause

**Site:** `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:676-684`
— the `else` arm commented *"Cross-module method: resolve via use_map →
import_map"* inside `compile_method_call_static` (fn starts ~:289).

The loop at **:678** scans **every** `use_map` entry for a key ending in
`.starts_with`, and **:680** takes the **first hit**, with **no receiver-type
check whatsoever**:

```rust
let method_suffix = format!(".{}", func_name);
for (raw, mangled) in ctx.use_map.iter() {
    if raw.ends_with(&method_suffix) && raw.len() > lookup_name.len() + 1 {
        resolved_name = Some(mangled.as_str());   // first hit wins
        break;
    }
}
```

If `common.bytes.span` is in the closure, `ByteSpan.starts_with` is in
`use_map`, so a bare type-erased `starts_with` resolves to it.

### Five independent proof steps (do not re-derive)

1. **It is Rust, not Simple.** The decision lives in `compiler_rust`. This is
   exactly why the two `.spl` patches were inert.
2. **MIR is byte-identical** between the working and broken cases.
   `SIMPLE_DUMP_MIR=probe` shows both emit
   `MethodCallStatic { func_name: "starts_with" }` — bare and unqualified. No
   MIR-lowering site *could* be responsible; the divergence is entirely
   downstream, in codegen.
3. **Pure-Rust seed reproduces it.** A 20 MB seed
   (`build/bootstrap/c5-b142/bootstrap-candidate/simple`), containing **no
   Simple compiler sources at all**, reproduces the exact split — independently
   confirming the bug lives in `compiler_rust`.
4. **Marker-symbol proof.** A fresh Rust seed built with five distinct markers,
   one per candidate resolution branch, fired **exactly one**:

   ```
   [MARK-A-USEMAP-SUFFIX] fn='probe' lookup='starts_with'
       raw='ByteSpan.starts_with' -> 'common__bytes__span__ByteSpan_dot_starts_with'
   ```

   Nothing fired for the control case.
5. **0.5s repro.** `<scratchpad>/mr/c.spl` (imports `ByteSpan`) vs `mr/g.spl`
   (no import). One variable; nothing about the calling code changes.

## Verification traps (the reusable value here)

**1. `dom_color.spl` alone does NOT reproduce — verifying with it is a FALSE
PASS.** Its entry closure never pulls in `common.bytes.span`, so it emits clean
`rt_string_starts_with` **even on a known-broken compiler**. Any A/B must use
an entry that imports **both** the text-predicate call site **and**
`common.bytes.span`. (The earlier "Reproduction" recipe in this doc leaned on
`dom_color.spl` as step 1 — that step proves nothing on its own.)

**2. Marker-symbol technique.** Emit a **uniquely-named symbol** from a
candidate site, build, and check with `nm`. This proves execution **without
relying on stdout**, which can be lost (see
`reference_native_build_eprint_lost`). This is what finally cracked it.

**3. "Code above executing code did not execute" was the clue the site was
wrong.** Markers inserted under a condition *strictly weaker* than a
provably-executing guard **never appeared**. When that happens, stop patching —
your model of which file runs is wrong, not your patch.

**4. Two `objdump` traps that produced a wrong conclusion here.**

- `objdump` prints **relative call targets WITHOUT an `0x` prefix** — pattern
  matching on `0x` misses them.
- These calls are emitted as **`movabs $addr,%reg; call *%reg`**, an indirect
  call through a register. **Searching the disassembly for `call <symbol>`
  finds nothing**, which produced one confident and completely wrong "this
  code is never called" conclusion.

Grep relocations, not disassembly text, when asking whether a symbol is
referenced.

**5. `--emit-archive` instead of a guest lane run.** Build any single module
with `--emit-archive` for `--target x86_64-unknown-none` (**~6s**, vs ~30
minutes for the guest lane) and inspect `nm -u` / relocations. Answers "what
does this code actually call?" and "did my compiler change do anything?"
before committing to a long run.

## Fix — IN FLIGHT

An agent is implementing an extension of the **`is_bare_builtin_collection_method`
veto** (`closures_structs.rs:76`, applied at `:364`): add the safe string
builtins **with arity**, so a **bare, type-erased receiver** reaches
`rt_string_starts_with` **before** any `use_map` resolution is attempted. The
veto is the correct layer — it short-circuits the suffix scan rather than
trying to make the scan smarter.

**Do not treat this doc as resolved** until an A/B on an entry importing
**both** shows `rt_string_starts_with` with `ByteSpan` in the closure.

### Mitigation to REVERT once the real fix lands

The **ByteSpan method-rename mitigation** was applied to dodge the collision by
renaming the colliding method. It is a workaround, not the fix. **Revert it
when the veto extension lands** — it must not be left as permanent scar tissue
in `common.bytes.span`, where a future reader would take the odd name for a
deliberate API choice.

### Regression test

Compile a module calling `.starts_with()` on a `.lower()` result **with
`common.bytes.span` in the entry graph**, and assert the relocation is
`rt_string_starts_with`. The `--emit-archive` route makes this a seconds-scale
test. Cover `ends_with` and `contains` too.

**Do NOT weaken a gate or a test.** Project rule.

## Related

- `doc/08_tracking/bug/interp_env_get_name_collision_nil_root_2026-07-26.md`
  — **same class**: a flat, name-keyed registry hijacking an explicit
  resolution. That one was for functions; this is the method counterpart.
- `.claude/memory` `feedback_interp_struct_name_collision_global_registry` —
  same-struct-name-in-two-modules collisions, the struct counterpart.
- `doc/08_tracking/bug/simpleos_freestanding_weak_rt_stubs_fail_open_2026-07-27.md`
  — the *other* root cause found in this guest campaign. Independent defect;
  both had to be fixed. Shares the `--emit-archive` diagnostic.
- Language rule (`.claude/rules/language.md`): "Chained methods on erased
  receivers … chains fail only when a link's receiver type is erased." This
  bug is that documented hazard biting inside the compiler's own resolution,
  not just in user code.

## RE-VERIFIED 2026-08-17 — DID NOT REPRODUCE

Fixture: a `struct ByteSpanLike` with its own `starts_with(self, p: i64) -> bool`
method declared in the same module as a `text.starts_with(text)` call, which is
the name collision this doc describes.

    R14 span   = true      (bs.starts_with(3), off == 3)
    R14 text   = true      ("hello".starts_with("he"))

Both dispatch correctly; neither call resolved to the other's implementation.
Run on the deployed seed AND consistent with a seed freshly built from current
source. `builtin_method_result_type`
(`codegen/instr/closures_structs.rs:1390`) also now classifies `starts_with`
as `TypeId::BOOL` on every receiver.

**Status: candidate CLOSE.** Not proven for every collision shape — only for a
user struct method colliding with a text builtin of the same name and arity in
one module. A lane with the original failing program should re-check before
closing outright.
