# Self-hosted parser has no `Variant = value` enum support — seed-only language feature
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** SUPERSEDED 2026-11-11 (lane p3-comp8) — explicit variant values are
implemented end-to-end in the self-hosted compiler at tip (parser arm,
discriminant storage, flat-AST bridge transport, `HirVariant` discriminant
lowering, C-codegen constant evaluator); absorber merge `9e7e7a526ed`
(PR #7597). Evidence in the dated addendum below.
**Found:** 2026-07-27 (bootstrap Stage 4 phase-2 parse, after device.spl entered the CLI closure)
**Area:** `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` (variant loop, ~:128)
**Severity:** high — a documented ABI pattern compiles under the seed but not the default toolchain

## Finding

`enum SyscallId: Exit = 0 ... Mmap = 10 ...` (explicit, non-sequential variant
values) parses under the Rust seed but the self-hosted parser rejects it:

```
[parser_error] line 8:10: expected enum variant name, got =
```

The variant loop handles payloads `Variant(field: type)`, pipe- and
comma-separated variants, but has no arm for `= <int>`. Deeper than parsing:
`decl_enum_def(enum_name, variant_names, 0)` stores **names only**, so even a
skip-the-value parser hack would silently assign ordinals — for
`src/os/kernel/types/syscall_types.spl` (gaps: 16→20, 38→44, out-of-order 43)
that would miscompile every syscall number. Do NOT "fix" this by skipping the
literal.

## Interim mitigation (landed 2026-07-27)

The only closure edge pulling the enum file host-side was
`os.userlib.device` → `new_device_info_buf`. Extracted `DeviceInfoBuf` +
factory to `src/os/kernel/types/device_info_types.spl` (enum-free), re-exported
from `syscall_types.spl` for kernel importers, repointed `device.spl`. The
guest kernel still compiles the explicit values via the seed cross-toolchain;
the host CLI closure no longer parses them.

## Real fix

Explicit variant values end-to-end in the self-hosted compiler: parser arm for
`= <int-lit>` (incl. hex/negative), value storage in the enum decl, HIR/codegen
using stored values, and cross-compiler parity specs against the seed on a
gap/out-of-order fixture. Until then any host-reachable module must not declare
explicit-value enums.

## Related

- `seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md`,
  `seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md` — same
  seed/self-hosted divergence family, all detonating at bootstrap Stage 4
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)


## Addendum 2026-11-11 — P3 lane comp8 verdict: SUPERSEDED (fixed at tip; verified in tree + seed-smoke)

Fresh verification on `origin/release/1.0.0` tip `dacccfc78fd10`
(worktree `simple-p3-comp8-20261111`), tracked seed build-commit
`46fe8f6b6def`:

- Parser arm (the filed symptom): `_ParserDecls/enum_module_body.spl`
  :601-607 — after each variant name, `if par_kind_get() == TOK_ASSIGN:
  parser_advance(); discriminant = parse_expr()`, then
  `variant_discriminants.push(discriminant)`; `:631` passes the array into
  `decl_enum_def(...)`. The `[parser_error] expected enum variant name, got =`
  rejection is gone. Values are NOT skipped — the discriminant expression is
  stored (this doc's "Do NOT skip the literal" constraint is honored).
- Storage: `decl_enum_def` (`_Ast/decl_nodes.spl:803`) stores the
  discriminant expression ids in the enum decl's FIELD_DEFAULTS slot
  (:841, :852).
- Transport: `_FlatAstBridge/module_assembly.spl:568-593` recovers
  "optional discriminant expression ids from FIELD_DEFAULTS", converts each
  via `convert_flat_expr`, and builds the staged `Variant` with
  `has_discriminant` / `discriminant`.
- HIR: `20.hir/hir_lowering/_Items/declaration_lowering.spl:947-956`
  (`lower_variant`) lowers each variant's discriminant expression into
  `HirVariant(has_discriminant:, discriminant:)` — stored values reach HIR.
- Codegen: `10.frontend/core/compiler/c_codegen.spl:48` imports
  `eval_enum_discriminant_expr`; the shared constant evaluator
  (`10.frontend/core/enum_discriminant_eval.spl`) handles int literals,
  named-variant/module-constant refs, unary/binary ops, casts, and
  bounds-checks shift amounts against i64 width.
- Provenance: `git log --follow` on `enum_discriminant_eval.spl` and
  `-S variant_discriminants` on the parser both resolve to merge
  `9e7e7a526ed` (PR #7597, 2026-11-07), which IS an ancestor of the release
  tip.
- Behavioral (seed-smoke, tracked seed, interpreter mode):
  `test/01_unit/compiler/frontend/enum_discriminant_shift63_spec.spl`
  parses a real explicit-discriminant enum declaration through the
  self-hosted parser (`parse_and_build_module`) and evaluates its
  discriminant expressions → 2/2 PASS.
- Gap/out-of-order parity note: no host-reachable module currently declares
  gap/out-of-order explicit values — `src/os/kernel/types/syscall_types.spl`
  `SyscallId` was rewritten sequential (`Reserved17` fills the old 16→20
  gap), so the interim mitigation stands and nothing in the host closure
  exercises gap/out-of-order discriminants. A dedicated gap/out-of-order
  parity spec remains a follow-up; the filed parser rejection defect itself
  is fixed and pinned by the shift63 spec.

Disposition: SUPERSEDED. Header flipped open → SUPERSEDED.
