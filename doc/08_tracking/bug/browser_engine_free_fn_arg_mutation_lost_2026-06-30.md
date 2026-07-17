# Class-instance args passed to free functions lose mutations in compiled library modules

- **Status:** PARTIALLY-RESOLVED (2026-07-17)
- **Discovered:** 2026-06-30
- **Area:** compiler backend (codegen / JIT) — value vs reference semantics for class-instance arguments
- **Severity:** High (silent data loss; corrupts any builder/visitor pattern that mutates an argument or accumulator)

## Summary

When a function defined in a **compiled library module** (i.e. a `.spl` reached via
`use std.…`, not the script's own `main` module) receives a **class instance as a
parameter** and mutates it — either via a `me`/`fn` method on that parameter or via
a free helper function — **the mutation is NOT visible to the caller**. The callee
operates on a copy. The same code runs correctly under the pure interpreter, which
is why script-level reproductions (which fall back to the interpreter) do not
trigger it.

This was found while reviving the DOM rendering adapter
`src/lib/gc_async_mut/web/simple_browser_page.spl`. The original adapter design
(1) parsed HTML, (2) walked the DOM mutating `data-simple-*` attributes onto nodes
(`_decorate_dom`), then (3) re-read those attributes during a layout walk that
pushed into a shared `collection` object. Both the attribute writeback and the
`collection.push` accumulation silently produced nothing.

## Minimal evidence (all observed in the real library-module execution path)

1. **Free-fn arg mutation lost (in-scope OK, caller sees nothing):**
   - `be_dom_set_attr(node, k, v)` (free fn in `dom_accessors.spl`): after the call,
     `be_dom_get_attr(node, k)` on the caller's node returns `""`.
   - The method form `node.set_attr(k, v)` persists when called **directly on the
     function's own parameter**, but NOT when that function is itself a library-module
     free function invoked from another library function.

2. **Direct mutation lost across a recursive writeback:** inside `_decorate_dom`,
   `node.set_attr("data-direct-test", "directval")` read back `'directval'`
   *in the same scope*, but was `''` by the time a later traversal re-read the same
   logical node (the `set_children`-based writeback up the tree did not propagate in
   the compiled module).

3. **Shared accumulator mutation lost:** `collection.targets.push(t)` reported
   `collection.targets.len() == 1` inside the callee, but the caller's
   `collection.targets.len()` was `0` after the call returned.

4. **Return values DO propagate:** restructuring the collector to *return* a
   freshly-built `SimpleBrowserCollection` (concatenating child returns) works
   correctly. This is the contrast that pins the bug to argument mutation, not to
   class instances generally.

5. **Interpreter masks it:** identical decoration/accumulation patterns, when run as
   a top-level script (`bin/simple run probe.spl`, which JIT-fails and falls back to
   the interpreter), persist mutations correctly. Only the imported library module
   exhibits the loss.

## Reproduction sketch

A library function `f(obj: SomeClass)` that does `obj.field = x` (or
`helper(obj)` which does so), called from another library function, then reading
`obj.field` in the caller → stale value. The same code in `main` works.

## Impact / who else is at risk

Any library-module code using the "pass an accumulator/builder and mutate it"
pattern, or a visitor that mutates nodes of a tree it received as an argument.
`dom_accessors.spl` is full of free-fn mutators (`be_dom_set_attr`,
`be_dom_set_style`, `be_dom_set_text_content`, `be_dom_add_child`, …) whose
mutations will be lost when invoked across library functions in compiled mode.
`be_dom_set_children` already returns a *new* node (a functional workaround),
suggesting this class of bug was hit before.

## Workaround applied (in `simple_browser_page.spl`)

The adapter was rewritten to be **purely functional**: a single `_collect` pass
walks the DOM + parallel layout boxes, derives the interaction model directly from
the *original* parsed attributes (which survive because they were set at parse
time, not via cross-fn mutation), threads form context + field-edit overrides down
as read-only parameters, and **returns** a concatenated `SimpleBrowserCollection`.
No DOM decoration, no shared mutable accumulator.

## Proper fix (compiler)

Class instances passed as function arguments must be passed by reference (or the
backend must propagate writes back) consistently between the interpreter and the
compiled/JIT path. Until then, library code must not rely on mutating a
class-instance argument and expecting the caller to observe it.

## Resolution (2026-07-17)

The compiler-side prerequisite landed 2026-07-14: `36aff72f4b1` (thread a
`mut`-param marker from the parser through HIR to `src/compiler/50.mir/_MirLowering/function_lowering.spl`,
which now binds `is_named_struct and (is_me_receiver or is_mut_param)`
parameters directly to the caller's incoming arg local instead of taking the
Bug #167 defensive value-copy). Per that lowering code's own inline note,
`is_named_struct` (`self.struct_field_order.has(type_name)`) is satisfied by
`class` declarations too today ("a `class` declaration currently lands in
`module.structs` too ... this copy therefore applies uniformly to every
`Named` aggregate param ... class included, until the upstream class/struct
conflation is fixed separately") — so marking a free-fn's class-typed param
`mut` is exactly the adoption vector for this bug.

Adopted in `dom_accessors.spl`: `be_dom_add_child`, `be_dom_remove_child`,
`be_dom_insert_before`, `be_dom_set_attr`, `be_dom_set_style`,
`be_dom_set_text_content` all now take `mut node`/`mut parent`. (Read-only
accessors and `be_dom_set_children`, which already returns a new node
functionally, were left unchanged.) The same latent pattern was found and
fixed in sibling script API files: `timer_api.spl`, `event_api.spl`,
`worker_api.spl`, `clipboard_api.spl`, `location_api.spl` — see the
companion bug doc `browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md`
for the full file list and per-file spec results.

**Verification caveat:** reproduced the exact documented symptom with the
seed oracle (`env -u SIMPLE_BOOTSTRAP bin/simple run <probe>`):
`be_dom_set_attr(node, "k", "v")` followed by `be_dom_get_attr(node, "k")`
returns `""` both before and after adding `mut`. Root-caused this to an
environment limit, not a defect in the adopted fix: the deployed
`bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`, 2026-07-11) is
confirmed (startup banner + `src/compiler_rust/driver/src/seed_warning.rs`
provenance) to be the Rust bootstrap seed, which predates and does not
contain the 2026-07-14 self-hosted-compiler fix (that logic lives only in
`src/compiler/*.spl`, compiled by `bin/simple build bootstrap`, which this
lane is forbidden from running). An isolated experiment confirms the split:
a `class`+`mut`-param mutation across two files compiled by the seed still
copies (unfixed, seed-only, previously undocumented limitation, independent
of `mut`), while the identical code in a single file works correctly under
the same seed (`mut` alone is honored intra-module). Adding `mut` does
remove the W1006-triggered whole-module interpreter fallback under the seed
(one real, observable improvement — the more severe of the two documented
failure modes), with zero regressions in `dom_accessors_spec.spl` (2/2
still pass) or any touched sibling spec. Full end-to-end proof requires a
self-hosted-compiled `bin/simple`, out of scope for this lane; filed as
follow-up, not blocking.

## Related

- `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` — free-fn mutators.
- Memory note: "Cross-module mutation loss — free fn(self: Class) across modules
  loses field mutation".
