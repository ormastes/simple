# Untyped text array element rejected from a `text` enum payload slot (2026-11-21)

**Status:** fixed in source, verification pending (compiler; fix on branch
`work/untyped-text-array-payload`, see "Fix" below). Source site already worked around by `8b3445e503b`
(`val read_paths: [text] = [...]` in `src/os/kernel/loader/spawn_recipes.spl`).
That annotation hides this defect; it does not fix it.

## Symptom

Full-CLI Phase 4 native-build (`boot-fable-lane-scripts/p4/cli-f23`, source
`8d850c22c54`):

```
enum construction 'os.kernel.types.capability_types.CapabilityKind.FileRead':
payload type mismatch at 0; function=spawn_recipe_grants
module=os.kernel.loader.spawn_recipes payload_at=.../spawn_recipes.spl:318:65
```

The payload really is `text`, so this is not a source bug.

## Minimal repro (reproduced, stage2 `pinned-8d850c22c549/.../integ23/.../stage2-admitted/simple`)

```
enum Cap:
    Read(path_prefix: text)
    Other
fn grants(root: text) -> [Cap]:
    var out: [Cap] = []
    val paths = ["/a", "/b"]          # unannotated
    for p in paths:
        out.push(Cap.Read(path_prefix: p))
    out
```

`native-build <f> --backend=cranelift --threads 1 --mode one-binary
--runtime-bundle core-c-bootstrap --emit-object`, run under a 12G cgroup and
taking about 0.5 s:

| variant | result |
|---|---|
| `[root + "/x", "/y"]`, `["/y", root + "/x"]`, `[root + "/x", root + "/y"]`, `[root, "/y"]`, `["/a", "/b"]` + for-in | mismatch at 0 |
| `["/a", "/b"]` then `val p = paths[0]` | mismatch at 0 |
| `val paths: [text] = [...]` | rc=0 |
| `[1, 2]` into the text slot (must reject) | mismatch at 0 (correct) |

`SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1` prints
`remembered ... expected='text' actual=''`. The element local has a
remembered HIR type that is *settled* but has no shape key (Any, TypeParam,
or another kind that `hir_type_shape_key` does not render). That makes
`enum_payload_local_compatible` (`enum_constructor_payload.spl`, the
`remembered_concrete_negative` branch) return false before it ever reaches
the MIR `Opaque(str)` evidence. The same build reports
`E-MC-ANY-002 ... resolves to Any in grants` for every failing variant and
does not report it for the annotated one. So the unannotated binding gets
`[Any]` somewhere on the native lane, and the element inherits `Any`.

## Where the fix belongs (not yet located)

The element must be typed `text` at its producer: the unannotated Let/array
literal type, or the for-in / index element's remembered HIR type. It must
not be fixed by admitting Any or unknown into a `text` slot, because that
would widen `any`.

Candidates to check with a trace build:

- the HIR `homogeneous_typed_array_element_type`
  (`20.hir/hir_lowering/_Expressions/expression_core.spl:343`). It needs
  `has_type_`, but HIR literals are built `has_type_: false` (`:1785`).
- the Let arm that remembers a settled `[Any]`
  (`50.mir/mir_lowering_stmts.spl`, `mir_let_type_unsettled` does not treat
  `Any` as unsettled).
- the for-in and Index element remember sites
  (`mir_lowering_stmts.spl` `lower_for_array_indexed`, `expr_dispatch.spl`
  Index arm).

Failing-first spec:
`test/01_unit/compiler/mir/untyped_text_array_enum_payload_spec.spl`. It
has not been executed: no full-CLI `simple test` binary exists on the host.
Whether the in-process lowering path reproduces the native-lane failure is
also unverified.

## Fix (2026-11-22)

Root cause: the first candidate. HIR lowers every literal with
`has_type_: false` (`expression_core.spl` wrapper at the end of
`lower_hir_expr`), so `homogeneous_typed_array_element_type` never typed a
text array literal. The unannotated binding then got no element type
(`binding_source_type` -> Error -> Let type `Infer`, symbol untyped), and the
loop / index element reached MIR with a settled no-shape remembered type.
Annotated `[text]` worked because the annotation supplied `[text]` to both
the Let and the symbol.

Fix: `homogeneous_typed_array_element_type` now accepts an untyped element
whose KIND proves `text` (`hir_kind_proves_text`: a string literal, a
`Var`/`NamedVar` whose symbol is declared `text`, or `a + b` with both sides
text). The literal is then `[text]`, so the Let type and symbol type equal
the annotated case. MIR's array-literal lowering ignores the literal type, so
codegen is unchanged. No other kind is inferred: numeric literals still take
their width from context, and Any/Error/Infer/Never still reject, so an
unannotated `[1, 2]` element is still rejected from a `text` slot and
nothing widens `any`.

Why the index read is covered by the same fix (old-stage2 traces,
`SIMPLE_ANYQ_PROBE=1 SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1`): for an all-literal
`val paths = ["/a", "/b"]` MIR records no initializer HIR type
(`early-Let remember ... init_hir_type=nil`), so the MIR Let arm takes the
`let_type` branch and remembers the Let type. Before the fix that type was
`Infer` (nothing remembered); after it, it is `[text]`, the exact state of
the annotated control (`val paths: [text] = ...` + `paths[0]` traces
`init_hir_type=Str ... remembered-accept`). Both the for-in
(`for_collection_declared_type`) and the Index arm (`find_local_hir_type` on
the base) read that remembered `[text]`.

Separate, NOT fixed here: an unannotated array of typed CALL results,
`val paths = [fa(), fa()]` with `fn fa() -> text`, already passes for-in but
`val q = paths[0]` is rejected the same way on the old stage2 (MIR records an
initializer element type from the call locals that is not `Str`, `q` lowers
I64 with a no-shape remembered type, and E-MC-ANY-001 fires on the index
expression). That path copies the initializer's metadata instead of the Let
type, so this HIR change does not reach it. File separately if it matters.

Verification state: NOT executed. The only runnable compiler on the host is
the old stage2 (`8d850c22c54`), which predates this source change; it
reproduces the defect only. The regression spec
(`test/01_unit/compiler/mir/untyped_text_array_enum_payload_spec.spl`, now
untagged) and the added HIR case in
`test/03_system/compiler/hir_homogeneous_array_type_system_spec.spl` must be
run once a Stage 2 built from this source exists. Close this record only
after that run.
