# Tauri Shell `tauri_mdi_bootstrap_has_drag_and_desktop_root` Stale CSS Assertion - 2026-07-07

## Status

Open (pre-existing, unrelated to P1.2 invoke-roundtrip work; discovered incidentally
while verifying `cargo test --lib` in `tools/tauri-shell/src-tauri`).

## Context

`tools/tauri-shell/src-tauri/src/lib.rs`'s `#[cfg(test)] mod tests` has
`tauri_mdi_bootstrap_has_drag_and_desktop_root`, which asserts:

```rust
assert!(js.contains("#wm-desktop{position:fixed;inset:0;overflow:hidden;z-index:10000"));
```

The actual CSS emitted by `tauri_mdi_init_script()` is:

```
#wm-desktop{position:fixed;inset:0 0 58px 0;overflow:hidden;z-index:10000;...}
```

(`inset:0 0 58px 0`, reserving 58px at the bottom for `#dock` — not `inset:0`).
The assertion string predates that dock-reservation change and was never updated.

## Evidence

```sh
cd tools/tauri-shell/src-tauri && cargo test --lib
```

Fails identically on `main` at commit `8e4d9c53ed` (verified via `git stash` /
re-run before any P1.2 edits were applied) — confirmed pre-existing, not a
regression from this session's invoke()-round-trip change:

```
thread 'tests::tauri_mdi_bootstrap_has_drag_and_desktop_root' panicked at src/lib.rs:2365:9:
assertion failed: js.contains("#wm-desktop{position:fixed;inset:0;overflow:hidden;z-index:10000")
```

## Required Fix

Update the assertion to match the current `inset` value (`inset:0 0 58px 0`) or
assert on a more change-resistant substring (e.g. just
`"#wm-desktop{position:fixed;"` plus a separate check for the dock-reservation
value). Not fixed here — out of scope for the P1.2 invoke() round-trip item;
flagged per repo convention rather than silently left red.
