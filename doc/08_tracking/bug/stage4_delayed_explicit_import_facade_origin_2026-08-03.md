# Stage 4 delayed explicit-import facade origin loses precedence

## Status and claim

CLAIMED — fix owner: `stage4_explicit_import_fix` on 2026-08-03. The owned
implementation surface is
`src/compiler/20.hir/hir_lowering/module_surface.spl`; the focused regression
surface is `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl`.

## Exact failure

The pure-Simple Stage 4 build stops during module-surface extraction with:

```text
Module surface extraction error: ambiguous facade export: module=app.io.mod item=context_generate package=app.io
```

The real graph is a delayed explicit-import chain across seven `context_*`
exports:

```text
app.io.mod --explicit context_generate--> app.io.cli_ops
app.io.cli_ops --explicit context_generate--> app.io.context_ops
app.io.context_ops --declares context_generate
```

The explicit route must select `app.io.context_ops` regardless of discovery
order. The collision is not a compatibility stub: the fixpoint incorrectly
indexes the `app.io.cli_ops` re-export surface as a second same-package owner
beside the concrete `app.io.context_ops` declaration.

## Root-cause hypothesis and acceptance

`module_surface_explicit_import_origin` recognizes only a direct declaration
on the imported owner, not an already-resolved `owner.export_origins` hop. The
fixpoint also skips a newly available delayed explicit origin instead of
writing it into `revisit_origins`, sibling inference runs while a matching
explicit route is still unresolved, and promotion indexes the re-export facade
instead of its concrete export-origin owner.

The fix is accepted only when all seven exact exports and an aliased delayed
chain resolve to `app.io.context_ops` in both real and reversed discovery order,
while an adjacent graph with no explicit route and two true sibling declarations
still fails closed as ambiguous. The fix must
remain in the pure-Simple module-surface owner; no Rust/runtime shortcut is
authorized. The focused suite must execute once after the repair, direct env
guards must pass, and no full Stage 4 build belongs to this isolated lane.

## Evidence

The pre-fix focused diagnostic exited 1 with 21 passed / 5 failed. After the
resolver repair, a detailed run proved the three new examples green: all seven
real `context_*` exports resolve through the delayed explicit chain, the
aliased reverse-order chain resolves to `app.io.context_ops`, and the no-route
two-sibling control still fails closed.

The encompassing suite remains 25 passed / 1 failed on its pre-existing
directory-sibling example. Its `lookup("sibling_value")` returns the valid
`SymbolId(0)`, but the old `to_be_truthy()` assertion interprets that numeric
payload as false. An attempted Option-presence assertion did not change the
Rust-seed interpreter verdict and was reverted so this fix does not absorb an
unresolved adjacent test-oracle issue. The three-cycle cap is exhausted; no
broader suite PASS or Stage 4 build is claimed by this isolated lane.
