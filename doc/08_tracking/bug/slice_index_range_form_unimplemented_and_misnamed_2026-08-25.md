# `a[start:end]` vs `a[start..]`: two unimplemented slice features, and one misnamed diagnostic (2026-08-25)

- **Status:** OPEN. Two genuine unimplemented features + one real diagnostic
  defect. Nothing here is "built wrong"; the wrong part is what the error says.
- **Severity:** MEDIUM — it is the blocker behind `#143` for
  `src/lib/common/text_advanced.spl`, and the misnamed message actively
  misdirects
- **Area:** `50.mir/_MirLoweringExpr/expr_dispatch.spl:1678`,
  `50.mir/_MirLoweringExpr/method_calls_literals.spl:2262-2275`
- **Found by:** continuing the `#143` chain after `75aaaf9252e`

## Matrix, every cell executed

| form | text receiver | array receiver |
|---|---|---|
| `s[1:3]` literal bounds | **works** -> `bc` | fails: `unresolved method call: slice` |
| `s[i:j]` variable bounds | **works** -> `bc` | fails: same |
| `s[2:]` open end | **works** -> `cde` | fails: same |
| `s[:3]` open start | **works** -> `abc` | fails: same |
| `s[2..]` / `s[1..3]` RANGE | **fails**: `unsupported array/string slice index a[start:end]` | fails: same |
| `.slice(1, 3)` explicit | (string path implemented) | fails: `unresolved method call: slice` |

A text receiver that is a **parameter** slices fine too (`fn take(s: text) -> text: s[1:3]` -> `bc`), so this is not the typed-parameter class that produced the rest of this chain.

## The diagnostic is misnamed, and that is the actual defect here

`expr_dispatch.spl:1678` reports:

```
unsupported array/string slice index a[start:end] (no native array-slice lowering; cannot safely lower to a value)
```

**`a[start:end]` on text is fully implemented and works.** The construct that
actually triggers this branch is the `..` RANGE form — `line[min_indent..]`.
The message names the syntax that works and never mentions the one that does
not.

This is not cosmetic. Chasing it cost eight fixtures built against the colon
form before the real trigger was found by probing
`self.builder.current_function` at the error site and reading the two offending
lines. Same failure mode as the empty-span defect
(`for_in_143_diagnostic_span_cannot_localize_the_loop_2026-08-24.md`): the
diagnostic cannot be used to find its own cause.

## Both gaps are "not built yet", not "built wrong"

Stated explicitly because the two need different dispositions and the repo's
TODO rules forbid renaming one into the other.

**Range index (`expr_dispatch.spl:1678`)** fails loudly ON PURPOSE. Its own
comment records why: `lower_range` is a known-incomplete stub whose emitted
callee is a bare `MirConstValue.Int(0)` that never resolves, so the subtree
would collapse to a placeholder `0` and the Index arm would `inttoptr`/GEP off
address 0 — a SIGSEGV. Failing the build is correct.

**Array `slice`/`substring` (`method_calls_literals.spl:2262-2275`)** is also a
deliberate exclusion. `a[1:3]` on a runtime array desugars to
`MethodCall(a, "slice", [1, 3])` and resolves Unresolved (arrays have no
registered stdlib `slice`), so without the `slice_recv_is_array` guard it fell
into the STRING fallback: the array handle got `rt_interp_cstr`'d and handed to
`spl_str_slice` as a char pointer — silently wrong output or an out-of-bounds
read. The guard converts that into a clean build failure. The comment states
plainly: "There is no dedicated array-slice runtime helper implemented."

So the work items are: implement `lower_range` for index position, and
implement an array-slice runtime helper. Neither is a bug to fix.

## Checked against the sibling Stage-2 resolution fix — different class

`unresolved method call: slice` looks like a name-resolution failure, and a
sibling lane had just fixed a resolution rule matching a qualified call on its
bare method name (with `str.to_bytes` a second victim). **This is not that.** It
is an explicit `not slice_recv_is_array` guard with a documented rationale, not
a name-keyed accident. Verified by reading the guard, not inferred from the
message.

## Rewriting `..` to `:` does NOT unblock the module

`text_advanced.spl` has exactly two range-index uses — `line[spaces..]` (:501)
and `line[min_indent..]` (:522), in `normalize_indent` and `dedent_lines`.
Swapping both to the colon form (which works today) was tried: the slice
failures go to **0**, and the 4-line reproducer then stops on the NEXT
unimplemented builtin, `unresolved method call: chars`.

So that swap is not landed. It would be a source workaround for an
unimplemented feature that buys nothing — the module is behind a queue of
independent feature gaps (untyped params -> range index -> `chars` -> ...), not
a single blocker. Recorded so the next lane knows the swap works and knows it
does not help.

## NOT verified

- The array `..` range form was not distinguished from the array `:` form
  beyond both failing; they fail at different sites and only the colon one was
  traced to the `slice_recv_is_array` guard.
- `chars` was not investigated at all beyond its message.
- Nothing here changes the MCP picture: still no binary, `#143` still at 7
  sites, and `borrow_check()` runs after `lower_to_mir` so the NLL false
  positive has never executed on this closure.
