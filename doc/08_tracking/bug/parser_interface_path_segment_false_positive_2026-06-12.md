# BUG: `interface` as dotted module-path segment trips TsInterface common-mistake error

## Closed 2026-09-13 — Fixed; `interface` as a dotted module-path segment now imports cleanly

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): `use std.common.torch.interface.{TorchBackend}` in a hello-world compiles and runs — output `ok`, exit 0. No `Common mistake detected: Replace 'interface' with 'trait'`.
- **inferred**: the entry's own status line already recorded "fixed + seed redeployed (2026-06-12)"; the recovery guard is present in both parsers per the Fix section.
- Note: the "adjacent latent cases" paragraph (`const`, `function`, `namespace`, `template`, `this` arms) is a separate hardening idea, not this defect; it was never observed firing.

- id: parser-interface-path-segment-false-positive
- date: 2026-06-12
- area: parser / error recovery
- severity: medium (blocks interpreter import of any module path containing `interface`)
- status: closed 2026-09-13 (fixed; verified). Originally: fixed + seed redeployed (2026-06-12); verified — `use std.common.torch.interface.{TorchBackend}` and the full `std.nogc_async_mut.gpu.*` chain now import cleanly in interpreter mode

## Symptom

`bin/simple run` (seed interpreter path) rejects any file importing a module
whose dotted path contains the segment `interface`:

```
use std.common.torch.interface.{TorchBackend}
```

fails with:

```
error: Common mistake detected: Replace 'interface' with 'trait'
  --> src/lib/nogc_async_mut/torch/backend.spl:11:22
```

This blocked the entire `std.nogc_async_mut.gpu.*` import chain in interpreter
mode (gpu/context.spl → torch.Stream → torch/backend.spl →
`std.common.torch.interface`), so specs for `nogc_async_mut/gpu/memory.spl`
and `context.spl` could not import the modules under test.

`bin/simple check` does NOT flag it — the false positive lives only in the
token-level recovery pass used by the parse path the interpreter takes.

## Root cause

`detect_common_mistake` flags `interface` whenever it appears as an
`Identifier` token, with no context check. As a module-path segment the
token is preceded and followed by `.`.

## Fix (both parsers, same commit)

- `src/compiler/10.frontend/parser/recovery.spl` — TsInterface arm now skips
  when `prev_kind == "Dot"` or next lexeme is `"."`.
- `src/compiler_rust/parser/src/error_recovery.rs` — same guard
  (`previous.lexeme == "." || next.lexeme == "."`).

## Verification

- Before: `bin/simple run` of a file with
  `use std.nogc_async_mut.gpu.device.{detect_backends}` exits 248 with the
  TsInterface error.
- After seed rebuild + redeploy of `simple_seed`: the torch interface chain
  and `gpu.memory` / `gpu.context` imports run clean (probe prints ok, exit 0).
- Genuine-mistake detection baseline unchanged: `interface Named:` was not
  flagged by `check`/`run` before the fix either (the common-mistake pass
  does not fire on that construct) — no detection regression introduced.

## Related discoveries during the fix

- The seed cargo build was broken by stale jj conflict markers in
  `src/compiler_rust/compiler/src/compilability.rs` (`mod tests` unclosed
  delimiter) — resolved by keeping side #1 (superset) in the same commit.
- `detect_backends()` still dumps core in the seed interpreter when calling
  `cuda_available()` on a host without libtorch CUDA — separate pre-existing
  interpreter-executor crash, NOT fixed by this parser change.

## Adjacent latent cases (same pattern, not yet hit)

`const`, `function`, `namespace`, `template`, `this` arms have the same
no-context check and would also fire on a module named e.g. `template.spl`.
Only `interface` is fixed here because it is the only segment name in use;
apply the same guard if another segment name collides.

## 2026-09-13 follow-up — the predicted `namespace` case has now been hit

The "Adjacent latent cases" section above proved correct. **measured** (Rust seed
`bin/simple` v1.0.0-rc.1, Windows): `src/app/ui.browser/dom_bridge.spl:119:89` uses
`namespace` as a named argument — `Element(node_id: nid, tag_name: tag_name,
attributes: attrs, namespace: "")` — and the unguarded TsNamespace arm rejects the
whole module with `Common mistake detected ... Use 'mod' for modules instead of
'namespace'.` This makes `app.ui.browser.dom_bridge` unloadable. Tracked under
`browser_dom_bridge_css_runtime_blocker_2026-06-14.md`; the guard needed is the same
shape as the `interface` one, keyed on named-argument position rather than `Dot`.
