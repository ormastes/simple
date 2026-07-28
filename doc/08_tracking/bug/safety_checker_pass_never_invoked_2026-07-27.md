# Bug: `safetychecker_check_module` (unsafe-context safety pass) has zero callers — no unsafe-boundary enforcement exists anywhere

**Date:** 2026-07-27
**Status:** fixed at warn level (2026-07-28, lane SF2) — the pass now runs BY
DEFAULT on every compile (driver.spl `lower_and_check_impl`): unset
`SIMPLE_SAFETY_WARN` = pass runs and emits a single summary line when
diagnostics exist; `SIMPLE_SAFETY_WARN=1` (legacy force-flag) = full
per-diagnostic listing; `SIMPLE_SAFETY_WARN=0` = pass skipped. It still only
`log_warn`s — it never pushes to `ctx.errors`, so it cannot fail a build.
All three declared rules are now implemented in `safety_checker.spl`:
`InlineAsmOutsideUnsafe` (now also covering `InlineAsmMatch`, previously the
wildcard no-op), `RawPointerOutsideUnsafe` (calls to `rt_ptr_read*`,
`rt_ptr_write*`, `rt_alloc`, `rt_free`, `ptr_add*`, `ptr_sub*` outside
`unsafe:`), and `UnsafeFfiOutsideUnsafe` (direct calls to module-local
`extern fn`s outside `unsafe:`; cross-module imported externs are NOT yet
tracked — name knowledge is module-local). The self-hosted (pure-Simple)
lexer+parser now also parses `unsafe:` / `danger:` blocks contextually
(core/parser_stmts.spl, EXPR_UNSAFE_BLOCK, bridged to ExprKind.UnsafeBlock —
same node the seed produces), so the checker sees unsafe scopes on both parse
lanes. `@unsafe(reason:, capabilities:)` on module-level fns is parsed and
recorded (metadata only, `parser_unsafe_annotations_get()` in
core/_ParserDecls/enum_module_body.spl); **gap:** block-level and
method-level `@unsafe` attachment is not captured (the decorator handler only
runs in the module-decl loop), and the metadata is not yet threaded into
HIR/decl arenas — enforcement/threading is future work. Fatal
(build-breaking) enforcement remains **blocked**: at least 23 owned files
have inline asm with no `unsafe:` block at all (see Migration blocker section
below and `doc/09_report/unsafe_enforcement_port_plan_2026-07-27.md`) and
must be remediated first. Specs:
`test/01_unit/core/parser_unsafe_block_spec.spl`,
`test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl`.
**Found:** side-finding while agents worked on other tasks, 2026-07-27
**Area:** compiler / semantics (`src/compiler/35.semantics/safety_checker.spl`) — unsafe-context enforcement
**Severity:** High — a security boundary that silently does nothing; neither compiler enforces it

## Finding

`safetychecker_check_module` (`src/compiler/35.semantics/safety_checker.spl:61`) is
never called from anywhere in the tree. A repo-wide grep for the symbol turns
up exactly one hit — its own `fn` declaration:

```
src/compiler/35.semantics/safety_checker.spl:61:fn safetychecker_check_module(self: SafetyChecker, module: HirModule) -> [SafetyError]:
```

No caller exists in `src/compiler/80.driver/driver.spl` or anywhere else in
`src/`. The entire unsafe-context safety pass — `SafetyChecker`,
`SafetyContext`, and the whole `safetychecker_check_*` family
(lines 43–373) — is dead code in the pure-Simple compiler pipeline.

The Rust seed (`src/compiler_rust/src/`) has no equivalent enforcement either:
there is no `*safety*` file under `src/compiler_rust/src`, and the only
`in_unsafe` hits in the whole `compiler_rust` tree are a build-script cfg
name from the vendored `anyhow` crate and an unrelated
`in_unsafe_block: bool` field on `AsyncContext` in
`src/compiler_rust/lib/std/src/verification/models/async_compile.spl`, which
has nothing to do with inline-asm/raw-pointer/FFI safety checking. So there is
currently **no unsafe-boundary enforcement in either compiler.**

### The checker also only implements one of its three declared rules

`SafetyError` (lines 17–22) declares three violation variants plus a generic
one:

```
InlineAsmOutsideUnsafe(span: Span)
UnsafeFfiOutsideUnsafe(span: Span)
RawPointerOutsideUnsafe(span: Span)
Other(message: text, span: Span)
```

Grepping the file for actual constructions of `SafetyError.*` finds exactly
one call site, line 143:

```
self.context.errors = self.context.errors.push(SafetyError.InlineAsmOutsideUnsafe(expr.span))
```

`RawPointerOutsideUnsafe` and `UnsafeFfiOutsideUnsafe` are declared and never
constructed anywhere in the file or the rest of the tree (confirmed via
repo-wide grep — the only two hits for each name are the enum-variant
declarations themselves). Raw-pointer and FFI safety checking do not exist
even in the dead code.

Additionally, the HIR has an `InlineAsmMatch` expression kind
(`src/compiler/20.hir/hir_definitions.spl:520`, lowered at
`src/compiler/20.hir/hir_lowering/expressions.spl:841`, consumed by MIR at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2602`), but
`safetychecker_check_expr`'s match (lines 129–369) has no `case InlineAsmMatch(...)`
arm — it falls through to the wildcard `case _:` at line 368, which is a
no-op. So even if the pass were wired up, asm-match arms would pass through
unchecked while only the single plain `InlineAsm(...)` expression form (line
141) is checked.

### Migration blocker if enforcement were flipped on fatally

Per `doc/09_report/unsafe_enforcement_port_plan_2026-07-27.md:129`, at least
23 owned files that use `asm` contain **no `unsafe:` block at all** — roughly
60 asm sites total, including kernel arch boot/trap/context-switch/syscall
files (`boot.spl`, `trap_vector.spl`, `context_switch.spl`,
`syscall_raw.spl`, x86 `io.spl`, per the plan doc's file table). A rough
repo-wide grep for the `asm` keyword outside vendored code turned up ~56
candidate `.spl` files (including a few doc/lint-only false positives), which
is consistent with that plan doc's ~38-owned-file estimate. Flipping the pass
on as a fatal (build-breaking) check today would immediately break the
SimpleOS kernel build across every one of those unguarded sites.

## Impact

The compiler currently makes no distinction between code that has been
audited as unsafe (inline asm, in the future: raw pointers, FFI) and code
that hasn't — `unsafe:` blocks exist syntactically but nothing checks their
placement. This is a silent no-op security boundary, not a partial one.

## Suggested fix

Do not flip this on as a fatal check directly — that breaks the kernel build
per the migration-blocker section above. The repo already has an established
convention for landing a fully-implemented-but-never-run checker safely: wire
it in warn-only and env-gated, exactly like the HM type-inference +
visibility-checker pass in `src/compiler/80.driver/driver.spl:970-989`
(`check_module_visibility`, gated behind `SIMPLE_TYPECHECK_WARN=1`, only logs
— never pushes to `ctx.errors`). Apply the same pattern here: wire
`safetychecker_check_module` into the driver behind a new env flag (e.g.
`SIMPLE_SAFETY_WARN=1`), measure the real diagnostic count across the ~993
modules, then use `doc/09_report/unsafe_enforcement_port_plan_2026-07-27.md`'s
per-file remediation table to backfill missing `unsafe:` blocks before ever
making it fatal. Separately, implement the two missing rule constructions
(`RawPointerOutsideUnsafe`, `UnsafeFfiOutsideUnsafe`) and add the missing
`InlineAsmMatch` case.

## Related

- `doc/09_report/unsafe_enforcement_port_plan_2026-07-27.md` — plan doc with
  the per-file asm-site/unsafe-block table backing the migration-blocker
  numbers cited above.
- `src/compiler/80.driver/driver.spl:970-989` — the existing repo convention
  for landing a fully-implemented, never-run checker as warn-only + env-gated
  instead of fatal.
