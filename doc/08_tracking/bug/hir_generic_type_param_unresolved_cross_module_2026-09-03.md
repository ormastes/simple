# HIR: a generic type parameter is treated as a missing named type across modules

Date: 2026-09-03
Compiler: `build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`
sha256 `fcf473728180d790bc6e15892c59cadf2f12600b4825575b30e3ff91c20bcf86`
Supersedes the "B3" entry of
`caret_suite_native_build_blocked_stage2_windows_2026-09-03.md` (that entry
called it a missing import; it is not).

## Summary

When a generic struct's `impl` methods are consumed from ANOTHER module, the
HIR cross-module callable dependency sweep treats the struct's GENERIC
PARAMETER as an ordinary named type, fails to find a declaration/import for it
in the owner module, and the failure resurfaces as a hard
`unresolved type: <param>` attributed to the importing module.

This is not a missing import in the stdlib. `Id` in
`src/std/common/search/types.spl` is the type parameter of
`struct PostingList<Id>` / `impl PostingList<Id>` — there is nothing to import.

## Minimal repro (14 lines, no stdlib involvement)

`m/t.spl`:
```
struct Box<Id>:
    ids: [Id]

impl Box<Id>:
    static fn new() -> Box<Id>:
        Box(ids: [])
    fn at(i: i64) -> Id:
        self.ids[i]
    fn merge(other: Box<Id>) -> Box<Id>:
        Box(ids: self.ids)
```

`m/main.spl`:
```
use t.{Box}

fn main():
    val b = Box(ids: [1, 2, 3])
    print(str(b.at(1)))
```

Build (see the SIMPLE_BOOTSTRAP note in
`native_build_requires_simple_bootstrap_env_windows_2026-09-03.md`):

```
[hir-callable-dep-origin-unresolved] owner=<pkg>.t dependency=Id: no
  declaration, re-export hop, or explicit import of this name in the owner
[hir-fatal] path=m/main.spl: unresolved type: Id
[hir-fatal] path=m/t.spl:  unresolved type: Id
[ERROR] phase 3 FAILED
```

Single-module control: the same generic struct + impl used only inside its own
file produces ZERO hir-fatals. The defect needs the cross-module hop.

## Where

`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
- `materialize_imported_callable_type_dependencies_inner` (~line 945) feeds
  every named type in a cross-module method signature to
  `materialize_imported_callable_dependency`, with no filter for the owning
  composite's type parameters.
- The advisory is emitted at line ~766 behind
  `not hir_dependency_is_builtin_type(dependency)` — that filter knows about
  builtins, not generic parameters.
- `ModuleSurfaceCallable.type_params` and `ModuleSurfaceComposite.type_params`
  both exist (`module_surface_types.spl:35,63,89`), so the owner's parameter
  names ARE available at the point the sweep runs; they are simply not
  consulted. `register_imported_type_methods_inner` already knows the owning
  composite name (`imported_name`).

## Impact

Blocks `native-build` of `src/app/slang_pack/main.spl` and
`src/app/llm_caret/agent_manager_view.spl`: after the B2 fix
(`f556f23aca4`), the ONLY remaining hir-fatals for slang are 11 x
`unresolved type: Id` from `src/std/common/search/{types,ranking}.spl`.
`ranking.spl` contains no occurrence of `Id` at all — it is an innocent
importer, exactly as the advisory predicts.

Platform-independent: pure-Simple HIR, nothing Windows-specific.

## Not fixed here — deliberately

The fix lands in the same resolver file another session is editing for the
devhub `invalid export origin` / `json_object_get` work. Filed with the minimal
repro rather than patched blind, because a `src/compiler/**` change cannot be
verified without a full self-hosted rebuild.

## Related, found by the same repro

The minimal SINGLE-module generic fixture (`struct Box<T>` + `impl Box<T>` +
`main` in one file) lowers cleanly through HIR and monomorphize and then the
compiler SEGVs (rc=139) after `[bootstrap-flat-entry] modules=1 functions=2`.
Same class as
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`, which is
cited in the materialization source itself (line ~1032). So fixing the HIR half
may only move a generic-using program's failure to a codegen SEGV.
