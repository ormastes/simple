# Tauri Shell `tauri_mdi_bootstrap_has_drag_and_desktop_root` Stale CSS Assertion - 2026-07-07
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Resolved (2026-11-25, verified by code inspection — see final section). The
emitted CSS no longer contains the dock reservation this assertion conflicted
with, so the assertion string matches again. Previously: Open (pre-existing,
unrelated to P1.2 invoke-roundtrip work; discovered incidentally while
verifying `cargo test --lib` in `tools/tauri-shell/src-tauri`).

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


## Verification 2026-11-25 (p2w6-ak lane, release/1.0.0 tip f3fb8f24dc9) — RESOLVED by inspection

The staleness no longer exists. The CSS emitted by `tauri_mdi_init_script()`
(`tools/tauri-shell/src-tauri/src/lib.rs:292`) is now:

```
#wm-desktop{position:fixed;inset:0;overflow:hidden;z-index:10000;pointer-events:none}...
```

i.e. back to `inset:0` — the `inset:0 0 58px 0` dock reservation this doc
reported is gone from the emitted style. The test assertion
(`tools/tauri-shell/src-tauri/src/lib.rs:2086`) checks
`js.contains("#wm-desktop{position:fixed;inset:0;overflow:hidden;z-index:10000")`,
which is an exact prefix of the emitted `textContent`, so the assertion
matches the current output. Verified by direct code inspection of both the
emitter and the assertion on release/1.0.0 tip; `cargo test --lib` was NOT
run (Rust builds are out of scope on this verification host), so this closure
rests on the string-level match, which is the entirety of the assertion.
