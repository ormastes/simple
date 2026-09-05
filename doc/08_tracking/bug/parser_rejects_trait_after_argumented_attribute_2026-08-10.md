# Parser rejects `trait` after an argumented attribute (`@doc("...")`)

**Status:** FIXED (2026-08-10)
**Found:** 2026-08-10 by stream M3, while fixing
`parser_rejects_pub_union_after_attribute_2026-08-10.md` (same root cause,
different missing arm).
**Component:** `src/compiler_rust/parser/src/parser_impl/items.rs`

## Symptom

```simple
@doc("x")
trait T:
    fn f(me) -> i64
```

fails with `Unexpected token: expected Fn, found Trait`.

## Root cause (shared with the union defect)

An attribute *with arguments* (`@doc("...")`) is parsed as a **decorator**, not
as a plain attribute, so it takes the decorator branch of
`parse_attributed_item`. That branch's post-decorator declaration match handles
`Class`, `Struct`, `Enum`, `Extern`, and `Mixin` and then falls through to
`parse_function_with_attrs`. `Union` was missing (fixed 2026-08-10) and `Trait`
is still missing.

Argument-less attributes (`@packed`) take the non-decorator branch, whose match
does handle both — which is why `@packed union` parses and `@doc("...") union`
did not, and why `@doc("...") trait` still does not.

## Unblock

Add a `TokenKind::Trait` arm alongside the `Union` arm. Unlike `Union` there is
no existing `parse_trait_with_attrs` helper, so one has to be introduced (or the
existing `parse_trait` reused and the attributes attached afterwards) — that is
why this was split out of the union fix rather than landed with it.

## Fix (2026-08-10)

Added `parse_trait_with_attrs` (mirrors `parse_mixin_with_attrs`: reuses the
existing `parse_trait()` and discards the attribute list, since trait
declarations have no place to attach them yet) in
`src/compiler_rust/parser/src/parser_impl/definitions.rs`, and added a
`TokenKind::Trait` arm to the decorator branch of `parse_attributed_item` in
`src/compiler_rust/parser/src/parser_impl/items.rs`, alongside the existing
`Union` arm, calling `self.parse_trait_with_attrs(attributes)`.

### Evidence

Built the Rust seed (`cargo build --release --bin simple` in
`src/compiler_rust`) with the fix and confirmed:

```
$ SIMPLE_RUST_SEED_WARNING=0 .../simple run /tmp/repro_case/r.spl
# (before fix) parse: Unexpected token: expected Fn, found Trait
# (after fix)  progresses past trait parsing to an unrelated later error
```

Sabotage-verified with a real regression spec,
`test/01_unit/compiler/parser/trait_with_argumented_attribute_spec.spl`
(a `@doc("...")`-attributed trait, an `impl Trait for Struct` implementing it,
and an `it` block calling the method):

- **With the fix reverted** (`git stash` of the two parser files, rebuilt,
  rerun):
  `SPEC FILE VERDICT: ... declared>=1 executed=0 passed=0 failed=1 dropped=1
  unrun=1 reason=parse-error`, with the exact original error text
  `Unexpected token: expected Fn, found Trait`.
- **With the fix restored** (rebuilt, rerun):
  `SPEC FILE VERDICT: ... declared>=1 executed=1 passed=1 failed=0 dropped=0`,
  `Results: 1 total, 1 passed, 0 failed`.

Landed to `origin/main`: parser fix (`items.rs`, `definitions.rs`) plus the
regression spec.
