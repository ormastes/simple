# Deployed stage4 compiler cannot resolve `.replace(...)` on an erased receiver in nested call context

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Filed:** 2026-07-26
- **Area:** compiler / stage4 self-hosted / method-resolution
- **Severity:** high (blocks the production host-WM Vulkan live-evidence gate)

## Symptom

Native-build of the host macOS WM Vulkan gate through the deployed stage4
self-hosted compiler (`bin/release/aarch64-apple-darwin-macho/simple`, per
`doc/09_report/wm_vulkan_host_2026-07-24.md`: `status: fail`, `reason:
production-native-build-failed`) aborts with:

```
error: semantic: method 'replace' not found on value of type str in nested call context
```

This was originally reported around line 2707 of
`build/wm_vulkan_host_2026-07-24/native-build.log` (that build-scratch log was
already rotated/cleaned by the time this doc was filed, so the exact
surrounding lines could not be re-captured — the transient `build/` dir does
not persist across sessions; the failing status is corroborated by the
committed evidence report doc referenced above).

## Root cause family (same as `web_font_provider_split_nested_call_resolution_2026-07-14`)

This is the same erased-receiver method-resolution gap already documented for
`.split(...)`, now hitting `.replace(...)` in the stage4 native-build lane
instead of the seed interpreter lane:

- `doc/08_tracking/bug/web_font_provider_split_nested_call_resolution_2026-07-14.md`
  — `.split(...)` on an erased `str` receiver fails with the identical
  diagnostic shape ("method 'X' not found on value of type str in nested call
  context") when the receiver appears as a nested call argument or at the end
  of a `.trim().lower()`-style chain.
- `doc/08_tracking/bug/interp_chained_replace_2026-07-05.md` — a prior,
  narrower `replace`-chaining regression in the seed *interpreter's* value
  dispatcher (`method_dispatch.rs`), resolved by adding `replace`/
  `replace_first` to the temporary-receiver dispatch table. That fix covered
  the interpreter's chained-call dispatch; it does not cover the stage4
  self-hosted compiler's *semantic checker* for nested call-argument
  positions, which is the lane failing here.
- Related also to the decode_string mangler single-candidate rebind defect
  (`src/compiler_rust/.../mangle.rs`, see
  `project_decode_string_stage3_method_resolution_defect_2026-07-13` in
  memory) — same family of erased-receiver / single-candidate method binding
  breaking down on builtin string methods once the receiver type has been
  erased through a nested expression.

The pattern: whenever a builtin `str`/`text` method call (`split`, `replace`,
`trim`, `lower`, …) is used as a nested argument expression — e.g.
`outer_call(x.replace(a, b))` or as the tail of a chain
`x.foo().replace(a, b)` passed into another call — the compiler's method
resolver loses the concrete `str` type of the intermediate result and fails
to find the builtin method, even though the same method resolves fine when
the call is split into a typed intermediate `val`.

## Reachable nested/chained `.replace(...)` sites (repo-wide, illustrative)

Grep across `src/lib`, `src/os`, `src/app` shows the compact nested/chained
form is common and not confined to one call site, consistent with the
codex-agent finding that patching individual helper call sites does not clear
the failure — other reachable sites keep tripping the same semantic check:

- `src/lib/nogc_sync_mut/play/wm/mod.spl:212` —
  `titles.push(line.replace("\t", " ").replace("\r", " "))` (chained
  double-`replace` result passed directly as a call argument — this is the
  textbook nested-call shape that trips the checker).
- `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:830,1072` —
  `DbValue.Text(value: rpt.replace(from_t, to_t))`.
- `src/lib/nogc_sync_mut/web_ui/dom_backend.spl:261` —
  `self.set_attr_value(element.id, "class", v.replace(class_name, "").trim())`.
- `src/os/tools/shell/sed/sed_tool.spl:61` —
  `write_line(terminal, line.replace(old_str, new_str))`.
- `src/app/io/jit_sffi.spl:156` / `src/app/io/jit_ffi.spl:156` —
  `arg_txt.push("\"" + a.replace("\"", "\\\"") + "\"")`.

The already-worked-around sites (split into typed intermediates per the
`interp_chained_replace` pattern) are `src/os/compositor/host_compositor_core.spl:256-258`,
`src/os/hosted/hosted_wm_evidence.spl:134-136`, and
`src/lib/common/ui/html_ui/doc_ops.spl:20-21` — but per the codex-agent report,
patching those did not clear the native-build failure, because the sites
above (and likely others reachable from the same build graph) still present
the compact nested form.

## Minimal repro attempt (2026-07-26)

Wrote `nested_replace/repro.spl` (a nested `wrap(s.replace(...))` call) and
ran it through two lanes:

- `bin/release/aarch64-apple-darwin-macho/simple run` (interpreter lane):
  **did not reproduce** — printed `hello there` successfully, both with a
  plain `wrap(s.replace(...))` and a chained `wrap(wrap(s).replace(...))`
  form.
- `bin/release/aarch64-apple-darwin-macho/simple build` (native-build lane,
  the lane the WM Vulkan gate actually uses): did not reproduce the exact
  `method 'replace' not found ... nested call context` diagnostic either —
  instead hit an unrelated `runtime error: field access on nil receiver` on
  both repro variants, indicating the isolated single-function repro doesn't
  exercise the same code path/module context as the real WM entry point
  (`src/os/hosted/hosted_entry.spl`) and its larger import graph.

Conclusion: reproduction requires the actual gate script
(`scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs` or the
sibling `check-macos-vulkan-2d-live-evidence.shs` / `check-macos-vulkan-web-live-evidence.shs`)
running the full `hosted_entry.spl` native-build graph, not an isolated
snippet — noted here rather than spending further time on isolation per the
time-box for this filing pass.

## Impact

Blocks `doc/09_report/wm_vulkan_host_2026-07-24.md`'s host macOS WM Vulkan
live-evidence gate at the native-build step (exit 1,
`production-native-build-failed`), before any snapshot/capture/input
evidence can be collected.

## Workaround status

**Insufficient.** A codex agent patched the individual helper call sites
already known to use chained `.replace(...)` (see the "already worked around"
list above) and the native-build failure persisted — other reachable nested
`.replace(...)` sites in the same build graph keep tripping the same semantic
check. This confirms the defect is a compiler-side method-resolution gap on
chained/nested string-builtin method calls in the stage4 native-build
semantic checker, not a source-level bug fixable by rewriting individual call
sites one at a time.

## Real fix (not done)

The stage4 self-hosted compiler's semantic checker must resolve builtin
`str`/`text` methods on erased receivers in nested call-argument and chained
positions — the same fix class called for in
`web_font_provider_split_nested_call_resolution_2026-07-14.md` for `.split`,
generalized to cover `.replace` (and likely other builtin string methods:
`trim`, `lower`, `starts_with`, …) wherever a method result is consumed
directly as a nested call argument rather than through a typed intermediate
`val`. Until fixed, every reachable nested/chained builtin-string-method call
site in the WM/Vulkan build graph would need the typed-intermediate
workaround simultaneously — which the codex-agent evidence shows is not a
tractable per-site patching strategy.

## Verification 2026-08-17 (content classification) — LIVE, site-patching duplicated

`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl`
still dispatches `.replace(...)` on an erased receiver at **two** duplicated
sites: the `if fname == "replace"` branch at line 914 (call at 925) and the same
branch again at line 1193 (call at 1204), both
`DbValue.Text(value: rpt.replace(from_t, to_t))`.

That the identical branch appears twice is consistent with the doc's finding
that per-site patching is insufficient — the sites multiply while the resolution
defect stays put. Root cause is stage4 method resolution in the native lowering
path, i.e. `src/compiler/**`, which is claimed by another lane. Recorded, not
patched.

Not proven: no `Results:` line — the repro needs a stage4 native build, which
was not run while the bootstrap holds the host.
