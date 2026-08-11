# `native-build` crashed on EVERY method call whose receiver has no inferred type — opaque `undefined field 'kind'` nil crash

Status: FIXED (2026-08-08), one-line `.spl` guard, verified live.

Found incidentally while investigating the UTF-8 slicing lane's `native-build`
divergence (`native_slice_splits_utf8_three_divergent_policies_2026-08-01.md`,
"Fence added 2026-08-08" section, item 6). That doc correctly separated the
finding into two questions and asked this one to be filed separately: is the
opaque nil crash itself a bug, independent of whether `.slice()`/`.substring()`
should be supported at all (a policy question, out of scope here, NOT touched).

## Summary

`bin/simple native-build --source <dir> --entry-closure --entry <dir>/main.spl
--cache-dir <c> --output <b>` crashed with an opaque, unhelpful internal error
on **any** method call (not just `.slice()`) whose receiver's HIR type was
absent — which is the normal case on `native-build`'s `--entry` fast path,
because that path never runs the HIR type-inference pass (30.types) that would
populate `HirExpr.type_`:

```
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
```

`bin/simple compile --native` on the same code does NOT hit this: it fails
closed earlier, at a separate whole-function pre-check, with a clean diagnostic
(`[CollectionOps]`) for constructs like bracket-slice it doesn't support at all.
The two "native" entry points therefore disagreed — one produces a
user-actionable diagnostic, the other an internal-looking crash that names
nothing about slicing.

## Root cause (PROVED, file:line)

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:940` (now
`:956` after the fix comment), inside `lower_method_call`, unconditionally
called:

```
if self.mir_hir_type_is_shared_resource(Some(receiver.type_)):
```

`HirExpr.type_` (`src/compiler/20.hir/hir_definitions.spl:430-436`) is an
Option-desugared field: statically typed `HirType` but paired with a
`has_type_: bool` companion, and it legitimately holds a bare `nil` when no
type was inferred — exactly the state on `native-build`'s `--entry` fast path
for every plain local (confirmed by the docstring immediately above this call
site, which already documents that this same fast path skips 30.types).

Wrapping that field in `Some(...)` converts an absent type (`nil`) into
`Some(nil)` instead of `None`. The callee,
`mir_hir_type_is_shared_resource(t: HirType?)`
(`src/compiler/50.mir/mir_lowering_stmts.spl:103-127`), pattern-matches on `t`:
`case Some(ht): match ht.kind: ...` / `case nil: false`. `Some(nil)` matches
the `Some(ht)` arm with `ht == nil`, so `ht.kind` is accessed on `nil` —
exactly the crash text.

This is a **general native-build defect**, not slice-specific: the call is
unconditional in `lower_method_call`, reached before any method-name dispatch.
Every sibling call site of the same helper pair passes the optional field
straight through, without the extra `Some(...)` wrap:

- `src/compiler/50.mir/_MirLowering/function_lowering.spl:217` —
  `self.mir_hir_type_is_resource(param.type_)`
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:919` —
  `self.mir_hir_type_is_resource(self.find_local_hir_type(close_recv_local.id))`

`method_calls_literals.spl:940` was the one outlier that added the wrap.

## Reproduction (ASCII only, no UTF-8 involved)

```
fn main():
    val s = "abcdef"
    val p = s[0:2]      # or s.slice(0,2) / s.substring(0,2) / s.starts_with("ab") / s.split(",")
    print("{p}\n")
```

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
  --source <dir> --entry-closure --entry <dir>/main.spl \
  --cache-dir <c> --output <b>
```

Pre-fix: `error: semantic: undefined field 'kind': cannot access field on
value of type 'nil'`, worker exits 1. By contrast `bin/simple compile --native
<file>` on the bracket-slice form fails closed cleanly: `cannot compile to
standalone native binary: 1 function(s) contain constructs that require the
interpreter: - main: [CollectionOps]`.

## Fix

One line, `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:956`:

```
-        if self.mir_hir_type_is_shared_resource(Some(receiver.type_)):
+        if self.mir_hir_type_is_shared_resource(receiver.type_):
```

**Fired-and-proved, not just "should work":**
1. Landed an unconditional `eprint("[mir-method-call] MARKER-PROBE-2026-08-08
   reached shared-resource-check\n")` immediately before the call, rebuilt with
   `native-build` on the bracket-slice fixture — the marker appeared in stderr
   immediately before the crash line, pinning the exact call as the crash site.
2. Applied the fix, same fixture, same command — exit 0, no
   `undefined field 'kind'` anywhere in the log, and the produced binary ran
   and printed `ab` (the correct `"abcdef"[0:2]` value).
3. Reverted the fix (`Some(...)` restored) on `.substring()` and
   `.starts_with()` fixtures — both crashed identically (`exit=1`,
   `undefined field 'kind'` × 2 in the log). Re-applied the fix, same two
   fixtures — both now exit 0 and produce correct output (`"ab"`, `true`).
4. Also tested `.split(",")` post-fix — exit 0, `.len()` on the result
   correctly reports `3`.

## Unexpected scope note

Fixing the nil crash did NOT merely surface the same `[CollectionOps]`
diagnostic on `native-build`'s path — it let `.slice()`, `.substring()`,
`.starts_with()`, and `.split()` **compile and run correctly** end to end
through `native-build --entry-closure`, producing working binaries with
correct output. The pre-existing `[CollectionOps]` fail-closed check in
`compile --native` lives at an entirely separate, earlier whole-function
pre-check that `native-build --entry-closure` never runs; once the spurious
nil crash was removed, the underlying MIR lowering for these methods turned
out to already work on this path. This does not touch or resolve the UTF-8
slicing byte/codepoint-boundary policy question (raw bytes vs lossy vs error)
documented in the cross-linked bug — that policy question remains fully open
and out of scope here; this fix only removed an accidental crash unrelated to
that policy.

## Family affected

Any method call reaching `lower_method_call` on `native-build`'s `--entry`
fast path with a receiver whose `type_` is nil (the common case — locals with
no explicit type annotation, since 30.types doesn't run on this path), UNLESS
it hits an earlier special-cased branch (`close` on a resource, or predicate
methods with a custom owner match before this line). Confirmed affected by
direct test: `s[0:2]` (bracket slice desugar), `.slice()`, `.substring()`,
`.starts_with()`, `.split()`. Not method-specific, not slice-specific, not
UTF-8-specific.

## Related

- `native_slice_splits_utf8_three_divergent_policies_2026-08-01.md` — the
  UTF-8 slicing policy bug that surfaced this finding incidentally; that doc's
  "Fence added 2026-08-08" section item 6 named this exact crash as a
  new-and-undocumented finding and asked for it to be filed separately. This
  doc is that filing. The UTF-8 byte/codepoint-boundary policy question that
  doc tracks is UNCHANGED and NOT addressed by this fix.
