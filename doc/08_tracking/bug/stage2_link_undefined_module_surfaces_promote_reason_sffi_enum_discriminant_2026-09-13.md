# Site 17: Stage 2 does not LINK on `origin/main` — `module_surfaces_promote_reason` and `_sffi_enum_discriminant` undefined

- Status: OPEN (2026-09-13)
- Area: Stage-2 native link (`--backend=llvm --mode=dynload`), pure-Simple symbol
  emission / `@always_inline` elision in `native_project`
- Found by: BOOT-16, run A (`build/bootstrap-boot16a`, branch head `4d51c3d3071`,
  18:37:13 -> 18:50), rc=1
- Blocks: Stage-2 **link**, so the candidate binary is never produced, the Stage-2
  sanity gate never runs, and Stage 3 / Stage 4 are unreachable. This is EARLIER
  than site 16, which is a sanity-probe failure on a candidate that exists.

## Symptom

```
Build failed: link failed: mold: error: undefined symbol: module_surfaces_promote_reason
mold: error: undefined symbol: _sffi_enum_discriminant
clang++: error: linker command failed with exit code 1 (use -v to see invocation)
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

`stage2-native-build.log` contains **no** `Build complete: N compiled` line — the
failure is at link, after compilation.

## Not caused by BOOT-16's seed change — measured, not argued

BOOT-16 landed `7bcf337209f` (enum runtime-identity remap in
`pipeline/native_project/mangle.rs`) in the same tree. A second bootstrap was run
from the IDENTICAL tree with only that file reverted to `origin/main` in the
working copy (`build/bootstrap-boot16b`, started 18:52:32, same canonical
`--full-bootstrap --backend=llvm --mode=dynload --jobs=16 --stop-after-stage2`
line). It fails **identically**, same two symbols, same exit:

```
bootstrap_b_control.log:37  | Build failed: link failed: mold: error: undefined symbol: module_surfaces_promote_reason
bootstrap_b_control.log:38  | mold: error: undefined symbol: _sffi_enum_discriminant
bootstrap_b_control.log:43  error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Only the one file differs between those two runs. The defect is on `origin/main`
(base `f4cd1c306dd`), and every lane building Stage 2 from today's `main` hits it.

## What the two names are

Both are **pure-Simple compiler functions**, not runtime externs, so this is not
the `rt_*` twin class that site 15 was. Neither is an emission bug: in both cases
the tree really does lack a reachable definition.

### `module_surfaces_promote_reason` — half-landed, then clobbered

`grep -rn 'fn module_surfaces_promote_reason' src/` returns **0**. The name exists
only as a re-export (`20.hir/hir_lowering/module_surface.spl:5`, an
`export use compiler.hir.hir_lowering.module_surface_registry.{...}` list) and as
an import + call (`80.driver/driver_source_pipeline_parsing.spl:33,585`). The
owning module, `module_surface_registry.spl`, does not contain the name at all.

It did. Counting occurrences of the name in that file per commit:

| commit | date | occurrences |
|---|---|---|
| `460aa9781cc` | 09-13 07:53 | 0 |
| `6a49e75efe0` "diag(compiler): name the surface, field and scope in a phase-2 promotion failure" | 09-13 08:51 | **3** |
| `db127a8e8c4` "fix(hir): stop module surface promotion failing on an already-persistent field" | 09-13 15:48 | **0** |

`6a49e75efe0` added the function (and `test/01_unit/compiler/hir/module_surface_promote_reason_spec.spl`,
which is still in the tree). `db127a8e8c4` is a **single-file** commit that rewrote
the same registry (+82/-102) and dropped it, while leaving the re-export, the
caller and the spec behind. That is the stale-snapshot clobber pattern
`.claude/rules/vcs.md` § "Sync must never clobber" describes: the second author
snapshotted a registry that predated the first author's addition. The fix is to
restore the function in `module_surface_registry.spl` (its content is recoverable
from `git show 6a49e75efe0:...`), not to touch the caller.

### `_sffi_enum_discriminant` — a private `@always_inline` helper called across a module boundary

An `@always_inline` one-liner wrapping `rt_enum_discriminant`, defined — not `pub`
— identically in `50.mir/_MirLoweringExpr/expr_dispatch.spl:38`,
`50.mir/_MirLoweringExpr/switch_operators_calls.spl:43` and
`70.backend/backend/_MirToLlvm/core_codegen.spl:104`.
`50.mir/_MirLoweringExpr/method_calls_literals.spl` **calls it at :372-374 and
defines it nowhere**; it reaches the name through
`use compiler.mir._MirLoweringExpr.expr_dispatch.*` /
`...switch_operators_calls.*` (lines 2-3), i.e. two wildcard imports that each
supply an identical private symbol. A call that crosses a module boundary is not
inlined, while the definition — being inline-only and private — is not emitted as
a linkable symbol in its own module, so the reference dangles. The same shape is
in `src/plugins/backend_vhdl/vhdl/vhdl_design_catalog.spl`.
Candidate fixes: make one definition `pub` and import it by name, or give
`method_calls_literals.spl` its own copy as its siblings have. `git log -1` on
that file names `13ca132a222` "chore(sync): session work products 2026-09-13"
(09-13 17:12) — another sync commit, so the same clobber class is a suspect here
too, but that is NOT established: the file has never defined the helper in any of
its last five commits.
## Reproduction

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=llvm \
  --mode=dynload --jobs=16 --stop-after-stage2 --output=build/<lane>
```
~13 minutes on a 20-CPU aarch64 host; the link failure is deterministic across the
two runs above.

## Why it is filed separately from site 16

Site 16 (`stage2_sanity_positional_route_k1_composition_admission_failed_2026-09-13.md`)
is a failure of the Stage-2 SANITY probe on a candidate that linked. This is a
failure to produce a candidate at all. Site 16's root cause has since been found
and fixed in the seed (see that record's 2026-09-13 addendum); this new link hole
is what now stands between the chain and a Stage-2 candidate, so the enum fix
could not be confirmed at Stage-2 scale by either BOOT-16 run.
