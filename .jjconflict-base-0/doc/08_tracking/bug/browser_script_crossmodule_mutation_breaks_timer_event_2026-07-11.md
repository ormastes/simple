---
id: browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11
status: PARTIALLY-RESOLVED
severity: medium
discovered: 2026-07-11
discovered_by: browser script API conformance probes (tools/pixel_compare/probe_xmod.spl, probe_bind.spl)
related: src/lib/gc_async_mut/gpu/browser_engine/script/timer_api.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl
---

# Cross-module class-arg mutation is lost under the seed interpreter — blocks setTimeout/addEventListener persistence

**Status:** OPEN. Interpreter/codegen limitation (the documented "class-arg
in-place mutation is unreliable cross-module" landmine). Blocks the browser
timer + event-listener APIs whose signatures cannot adopt the return-value
workaround.

## Summary

A `pub fn` in module A that mutates a class/collection argument (either by
direct field write or by calling a `me` method) does **not** persist the
mutation back to the caller in module B under the seed interpreter (JIT rejects
it with `W1006: mutation without mut capability` and falls back to an interpreter
that copies the argument by value).

Two workarounds exist and were applied where signatures allowed:
- **return-value**: `x = f(x)` — used for storage/console/dom mutators.
- **`mut` param**: `f(mut x)` — requires the caller pass a `var`.

`set_timeout(loop, id, ms) -> i64` and `node_add_event_listener(node, …)` can
use neither cleanly: `set_timeout`'s return slot is the timer id (cannot also
return the loop), and the specs call the event/timer functions in **statement
position on `val` bindings** (so `mut` is a compile error and there is no
reassignment to receive a returned value). The mutation is therefore lost.

## Minimal repro

```
# probe_xmod.spl — cross-module mutator, effect lost
var s = BrowserStorage.new()
storage_set_item(s, "k", "v")     # (pre-fix void signature)
storage_get_item(s, "k")          # => nil  (mutation did not persist)
# JIT: "W1006: mutation without mut capability ... while lowering storage_set_item"
```

```
# probe_bind.spl — direct me-call persists (I), cross-module fn does not (J)
var p2 = BeDomNode.element("div"); p2.add_child(BeDomNode.element("span"))
var ex2 = p2.children[0]
ex2.set_attr("k", "v")            # PASS (direct me-call)
node_set_attribute(ex2, "k", "v") # (pre-fix) FAIL (cross-module fn param)
```

Observed failures: `timer_api_spec` (fires/repeats/rAF register — 8 failed),
`event_api_spec` (adds/capture listener — 2 failed).

## Resolution (2026-07-17)

Two compiler fixes landed 2026-07-14 that are the prerequisite for this bug:
`743fc0e2bfa` (fix `me`-receiver mutation conflation) and `36aff72f4b1`
(free-fn `mut s: Struct` param now binds by-reference instead of taking the
Bug #167 defensive value-copy in `src/compiler/50.mir/_MirLowering/function_lowering.spl`).
That MIR-lowering fix explicitly applies to `Named` aggregate params
`is_named_struct and (is_me_receiver or is_mut_param)` — and, per its own
inline comment, `is_named_struct` is satisfied by BOTH `struct` and `class`
declarations today (a documented, separate class/struct-conflation gap), so
a `class`-typed free-fn param marked `mut` gets the same by-reference bind as
a struct.

Adopted here: all five `timer_api.spl` free functions (`set_timeout`,
`set_interval`, `clear_timeout`, `clear_interval`, `request_animation_frame`)
and `event_api.spl`'s `node_add_event_listener` / `node_remove_event_listener`
now declare their `EventLoop`/`BeDomNode` parameter `mut`, matching the
landed fix's contract. No call sites needed changes — `val`-bound arguments
(as already used by `timer_api_spec.spl`/`event_api_spec.spl`) bind to `mut`
params without error under the seed oracle.

**Verification caveat (environment-limited):** the currently-deployed
`bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`, dated 2026-07-11)
is confirmed via its own startup banner and `git blame` (`src/compiler_rust/driver/src/seed_warning.rs`)
to be the Rust-built bootstrap **seed**, which predates and does not embody
the 2026-07-14 self-hosted-compiler commits above (those live only in
`src/compiler/*.spl`). Under the seed:
  - **Before:** `timer_api_spec`/`event_api_spec` reproduce exactly the
    documented symptom (`[INFO] JIT compilation failed, falling back to
    interpreter: ... W1006 ...`, then the mutation is lost — 8 and 2
    failures respectively, e.g. `set_timeout` leaves `pending_timer_count()
    == 0`).
  - **After (source adopts `mut`):** the W1006-triggered whole-module
    interpreter fallback is gone (JIT now compiles the module cleanly), but
    the SAME failure counts persist (8 and 2) — the seed's own JIT/codegen
    has an independent, previously-undocumented cross-module class-arg copy
    limitation that is untouched by `mut` (confirmed via an isolated
    single-file vs. cross-module-import experiment: same-module `mut node:
    Box` mutation persists correctly on the seed; the identical code split
    across two files does not, regardless of `mut`).
  - This is expected: hard rules for this lane forbid `bin/simple build`/
    `bootstrap`, so no binary that embodies the landed self-hosted-compiler
    fix could be produced or exercised to close the loop end-to-end. The
    source-level adoption is correct and matches the fix's documented
    design; a self-hosted-compiled `bin/simple` is required to observe the
    actual behavior change. Filed as follow-up, not blocking this adoption.
  - Zero regressions: failure counts are byte-identical before/after across
    `timer_api_spec.spl`, `event_api_spec.spl` (both `test/01_unit/browser/script/`
    and the legacy `test/unit/browser/script/` copies), confirming the `mut`
    additions are safe no-ops under the seed and forward-compatible with the
    self-hosted compiler.

Sibling files with the identical latent pattern (plain non-`mut` free-fn
class param, mutated via field write or `me`-call, called in statement
position) were found and fixed the same way: `worker_api.spl`
(`worker_post_message`, `worker_receive_message`, `worker_terminate`),
`clipboard_api.spl` (`clipboard_write_text`), `location_api.spl`
(`location_assign`, `history_push_state`, `history_replace_state`,
`history_back`, `history_forward`, `history_go`). `dom_api.spl`,
`storage_api.spl`, `console_api.spl` already use the sanctioned
return-value workaround (`x = f(x)`) and needed no change.

Left for follow-up (out of scope / higher risk, not touched):
- `location_api_spec.spl`'s "assigns a new location" / "reload refreshes
  parsed fields" cases fail for an **unrelated** reason: the spec expects
  `location_assign`/`location_reload` to *return* the mutated
  `BrowserLocation` (`val next = location_assign(loc, url)`), but the
  current source is void. This is a pre-existing spec/source signature
  mismatch, not the cross-module-mutation bug — fixing it means choosing
  between the return-value convention and the `mut`-in-place convention,
  which is a design decision out of this lane's scope.
- `script_runner.spl`'s `script_runner_clear_dirty(runner: ScriptRunner)`
  has the same latent single-param pattern but lives in a file whose own
  comments document a *different*, deeper landmine (module-level `var`
  writes not persisting across calls) touching the JS engine wiring —
  left untouched pending a dedicated look.
- `worker_api_spec.spl` has 5 pre-existing failures, all `function not
  found` (`worker_is_secure_context`, `worker_create_with_secure_context`,
  `worker_global_scope_create`) — unrelated to this bug, untouched.

## Correction (2026-07-17) — root cause narrowed, "cross-module" framing was wrong

Follow-up isolation (T3 lane, SSpec regression-spec sweep) found the
"Verification caveat" above mischaracterizes the trigger. Cross-module
`mut`-param class mutation (including `set_timeout`/`EventLoop`) actually
**works correctly** when called from a plain standalone `fn main()` script —
it is NOT a general cross-module limitation. The real trigger is calling the
mutating function from inside a `std.spec` `it` block specifically (SSpec's
own harness plumbing, not module boundaries). See
`doc/08_tracking/bug/sspec_it_block_loses_cross_module_class_mutation_2026-07-17.md`
for the full repro and narrowing. The `mut` adoption in this commit remains
correct and necessary; only the stated root cause needed correcting.

The standalone behavior now has a checked-in positive control at
`test/fixtures/browser/event_loop_set_timeout_standalone.spl`, wired through
`scripts/check/check-gui-hardening-open-gates.shs`, requiring exactly one
output line equal to `tid=1 pending=1`, and through the pure-Simple staged
bootstrap workflow with byte-exact output. The only retained OPEN SSpec guard is the existing
"schedules a one-shot timer" assertion in
`test/01_unit/browser/script/timer_api_spec.spl`; it is not run in green CI
and is not marked as an expected failure. Promote that existing spec into a
green gate, and remove this SSpec caveat, only after it passes with the same
runtime as the standalone control. The standalone control remains afterward
as the browser API mutation regression test.

## Expected

Cross-module mutation of a class/collection argument via a `me` method or field
write persists to the caller (matching the compiled-binary semantics), so
`set_timeout`/`addEventListener` register on the caller's live loop/node.

## Related value-copy limitation (DOM handles)

`BeDomNode` is a value type and `document_get_element_by_id` /
`document_query_selector` return a value-copy extracted from the tree. Even
with the return-value mutator convention, `n = node_set_attribute(n, …)` mutates
the copy — a subsequent **re-query of the tree does not observe the change**.
The single most common real-page idiom,
`document.getElementById('x').innerHTML = …`, therefore cannot be made to
persist to the live tree through the current handle-based API. A durable fix
needs reference-typed DOM nodes (dom.spl) or a mutate-in-place-by-id API
(`document_set_*_by_id(root, id, …) -> BeDomNode`). The conformance matrix's
mutation rows all use build-then-query or same-`var` reassignment, which work;
mutate-then-requery does not.
