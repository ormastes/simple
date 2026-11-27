# Unsafe block expression binding parser gap

Status: FIXED 2026-11-11 (lane p3-comp9) — the parser now accepts
`unsafe(capabilities: [...]):` block expressions in value position
(`parse_unsafe_block_expr_if_present`, src/compiler/10.frontend/core/parser_stmts.spl:644-723),
records the capability set into HIR, and three pinning specs pass on the tracked
seed (46fe8f6b6def): unsafe_call_argument_parser_spec 8/8 (incl. the exact
`val reference = unsafe(capabilities: [ffi]): ...` binding form),
unsafe_block_expression_spec 5/5, unsafe_block_binding_type_spec 3/3. Native
parity / zero-cost evidence remains lane-gated (see addendum).

The supported expression form

```simple
val handle = unsafe(capabilities: [ffi]):
    spl_mutex_create()
```

is rejected by the current deployed parser at the block colon. This prevents a
zero-overhead expression-scoped FFI boundary from binding its validated raw
result directly. The temporary migration form declares a typed local and
assigns it inside the lexical unsafe block. The optimizer must prove the initial
zero store dead before this workaround is accepted for a measured hot path.

Required fix: parse `unsafe(...)` block expressions wherever an ordinary value
expression is accepted, preserve their capability set in HIR, and add
interpreter/JIT/native parity plus generated-code evidence that the block itself
has no runtime cost.

The gap is compilation-context dependent: direct checks of process-governor
and compiler-driver modules currently lower the same lexical block spelling as
a call to a missing function named `unsafe`. Those sites must temporarily use
function-level `@unsafe(... capabilities: [ffi])`, which widens authority but
does not add runtime work. The parser/lowering fix must make lexical blocks
portable across module families before these scopes can be narrowed.

## Addendum 2026-11-11 — P3 comp9 lane triage (worktree simple-p3-comp9-20261111, base 77be2266752d)

**Verdict: FIXED.**

Required-fix items, re-verified at the lane base:

1. "Parse `unsafe(...)` block expressions wherever an ordinary value expression is
   accepted" — DONE. `parse_unsafe_block_expr_if_present`
   (src/compiler/10.frontend/core/parser_stmts.spl:644-723) is hooked into primary
   expression parsing (`_ParserPrimary/primary_expr.spl:554-557`, keyword `unsafe` and
   `danger`), parses both the bare `unsafe:` and the `unsafe(reason: "...",
   capabilities: [ffi, raw_ptr]):` forms, rolls back cleanly on no-match, and emits
   `expr_unsafe_block_with_caps(body, unsafe_caps, 0)` with the capability list. The
   two merges that landed this code (9e7e7a526ed PR #7597 for the contextual parser
   entry, 820631c6e5c7 PR #7545 for the caps-carrying node) are both ancestors of the
   lane base — verified fresh, not assumed.
2. "Preserve their capability set in HIR" — DONE. The caps are recorded at parse
   (`representation_record_region_v1(unsafe_caps)`) and the HIR transport is pinned by
   `test/01_unit/compiler/hir/unsafe_block_binding_type_spec.spl` (HirExprKind.UnsafeBlock
   binding-type transport incl. nested unsafe/nograd blocks) — 3/3 PASS on the tracked
   seed (bin/simple.exe @ 46fe8f6b6def, `--mode=interpreter --no-cache`).
3. Regression evidence, all green on the tracked seed:
   - `test/01_unit/compiler/frontend/unsafe_call_argument_parser_spec.spl` 8/8 —
     includes the exact repro family from this row (`val reference =
     unsafe(capabilities: [ffi]): async_ref_from_core_i64(scope, entry)`), nested
     value-position forms, named-argument forms, and malformed-shape rejections
     (missing colon, non-ident caps).
   - `test/01_unit/compiler/interpreter/unsafe_block_expression_spec.spl` 5/5 —
     end-to-end value semantics of `val x = unsafe:` block expressions (last
     expression is the value), the historical `semantic: function 'unsafe' not found`
     failure mode.
   - `test/01_unit/compiler/hir/unsafe_block_binding_type_spec.spl` 3/3 (above).

Residual, left as follow-up (not blocking): the doc's secondary asks —
interpreter/JIT/native parity and generated-code evidence of zero runtime cost for
the block itself — have interpreter parity and HIR pins only. Native/JIT parity
evidence needs entry-closure native builds, which are forbidden in this lane
(same grant class as the campaign-wide native-verification debt); no in-tree
native unsafe-block pin exists yet.

Disposition: FIXED. Header flipped Open → FIXED 2026-11-11 (lane p3-comp9).

## Addendum 2026-11-13 — lane p3-comp1 (worktree p3comp1-wt)

Concurs with the comp9 lane's FIXED verdict; independently re-verified the three
pinning specs on this lane's binary (tracked seed @ 46fe8f6b6def):
`unsafe_call_argument_parser_spec` 8/8, `unsafe_block_expression_spec` 5/5,
`unsafe_block_binding_type_spec` 3/3. No in-lane change.
