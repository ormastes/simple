# Team Clippy Doc Progress

## Batch 1 — 2026-04-28

### Files Fixed

| File | Warnings Before | Warnings After | Lint |
|------|----------------|----------------|------|
| `src/compiler_rust/driver/src/main.rs` | 7 | 0 | `doc_overindented_list_items` |
| `src/compiler_rust/compiler/src/codegen/instr/body.rs` | 1 | 0 | `doc_lazy_continuation` |

**Total: 8 warnings eliminated**

### Changes Made

- `driver/src/main.rs` lines 24–27, 30, 37, 42: Reduced continuation indentation
  from deep alignment (40+ spaces) to 4 spaces after `//!` on list-item continuations.
- `compiler/src/codegen/instr/body.rs` lines 47–49: Rewrote doc comment to avoid
  lines starting with `+` (which Clippy treats as lazy list continuations). Replaced
  `Comparisons + membership + identity` phrasing with comma-separated form.

### Verification

```
cargo clippy --no-deps -p simple-driver ... -W clippy::doc_overindented_list_items -W clippy::doc_lazy_continuation
# → 0 matches

cargo clippy --no-deps -p simple-compiler ... -W clippy::doc_overindented_list_items -W clippy::doc_lazy_continuation
# → 0 matches
```

### Notes

- `simple-runtime` crate: no warnings found (0 matches).
- `driver/src/log.rs`: no warnings found (0 matches).
- Warnings only surface when the lints are explicitly enabled (`-W`); they are not
  in the default Clippy deny list for this workspace yet (Team Allow-Config scope).
- Did not touch `Cargo.toml` (Team Allow-Config scope).
- Did not touch any non-doc `simple-compiler` warnings (Team Compiler-Manual scope).
