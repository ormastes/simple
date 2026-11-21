# Untyped text array element rejected from a `text` enum payload slot (2026-11-21)

**Status:** open (compiler). Source site already worked around by `8b3445e503b`
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
