# Default Trait Placeholder Burn-Down

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 194 slice
**Status:** Fixed slice; parent backlog remains open

## Research

- Row 194 tracks a broad placeholder-test backlog and should not be closed after one file.
- `test/unit/compiler/parser/default_trait_method_spec.spl` had two dummy assertions using `expect(true).to_equal(true)` and one `pass_do_nothing` placeholder.
- The same spec already defines executable wrapper functions for default trait behavior, so the dummy assertions can be replaced with real checks without changing parser or trait implementation code.

## Plan

- Replace dummy assertions with concrete assertions over existing wrapper behavior.
- Add small helper functions for expected trait structure counts.
- Verify with lint, focused test, and a placeholder-pattern scan for the edited file.
- Annotate row 194 with this issue key while keeping the parent backlog open.

## Fix

- Replaced two dummy assertions and removed one placeholder empty-impl body in `default_trait_method_spec.spl`.
- Added concrete checks for mixed default methods and all-default trait impl behavior.
- Left row 194 open because it represents a repo-wide backlog, not a single-file item.

## Verification

```sh
bin/simple lint test/unit/compiler/parser/default_trait_method_spec.spl
bin/simple test test/unit/compiler/parser/default_trait_method_spec.spl
rg -n "expect\\(true\\)\\.to_equal\\(true\\)|expect\\(false\\)\\.to_equal\\(false\\)|pass_todo|pass_do_nothing|pass_dn" test/unit/compiler/parser/default_trait_method_spec.spl
```
