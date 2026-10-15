# C36 monomorphization API owners

Issue: https://github.com/ormastes/simple/issues/3021

Base: `aeb2517fac0a3f287aed4347d75235ac8976161d`.

The frozen C36 `compiler-driver` and `bootstrap-k1-selected` HIR fatal groups
both report `module error has no exported item CompileError` for
`src/compiler/40.mono/monomorphize/deferred.spl` and unresolved `type_Simple`
(lines 328, 374) / `type_Pointer` (362) for the sibling `util.spl`.
Evidence root:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-reviewed-fixes/`.

## Bounded candidate

Remove the unused `use error (CompileError)` import from deferred. Its only
CompileError reference was that import. Errors already use deferred_subst's
`deferred_set_error`, `deferred_clear_error`, and `deferred_last_error`, with
nil/bool results. The actual CompileError definition is in
`src/compiler/00.common/error.spl:108`; importing it adds no required behavior.

The behavioral regression
`test/01_unit/compiler/mono/monomorphize/deferred_missing_template_error_spec.spl`
checks that an absent template returns nil and preserves its exact diagnostic.

## Unresolved util migration

Do not merely rename the three missing helpers to `Type.Simple`/`Type.Pointer`.
The imported `compiler.frontend.parser_types_expr.Type` is a struct at lines
54-57, containing `kind: TypeKind` and `span: Span`. TypeKind declares
`Named(text, [Type])`, `Pointer(Type, bool)`, `Reference(Type, bool)`, `Atomic`,
`Isolated`, and `Weak`. The utility's legacy enum constructors and matches
must be migrated as a coherent adapter, preserving nested conversion,
primitive normalization, generic bindings, and all eight ConcretePointerKind
meanings. A source-span policy and the opaque Handle representation need
explicit decisions before the old adapter can be replaced safely.

## Validation and handoff

Source inspection only. Regression authored but unexecuted; no compiler,
native build, or test execution in this lane. Independent landing review and
the parent owner's affected-file manual compile remain required. This candidate
only addresses deferred.spl; util.spl remains unchanged and issue #3021 stays
open. Main-worktree dirty changes and the frozen C36 worktree were preserved.
