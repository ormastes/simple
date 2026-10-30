# `simple run` JIT: a facade `__init__.spl` under a numbered layer dir is never flattened (unresolved external `any_escape_check`)

Status: FIXED (work/jit-reexport-resolve-fable-20261030) -- see "Fix".

- Filed: 2026-10-30, macOS hello native-build lane (next blocker after
  CODEGEN-AMBIGUOUS-METHOD, see `work/seed-trait-dispatch-fable-20261030`)
- Severity: P2 -- results stay correct, but the WHOLE compiler worker
  (6,810 functions in the probe below) silently drops to the interpreter,
  so `native-build` runs the Simple-written compiler ~100-1000x slower.
- Engine: Cranelift JIT lane only (`bin/simple run`, the lane
  `native-build` uses to execute `src/app/cli/native_build_main.spl`).
  The interpreter lane and the AOT native-project lane are NOT affected
  (their resolvers already handle this shape; see "Why only this lane").
- Component: `src/compiler_rust/compiler/src/pipeline/module_loader.rs`,
  `resolve_numbered_parts_from_root`, last-segment branch (`if is_last`).
- Platform: platform-independent (pure `Path` logic; measured on
  aarch64-apple-darwin).

## Symptom

```
[jit-fallback] unresolved external symbol 'any_escape_check': whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: unresolved external symbol 'any_escape_check' would NULL-jump in JIT; deferring to interpreter
```

`any_escape_check` is a `pub fn` in
`src/compiler/35.semantics/any_escape/checker.spl`, re-exported by the
package facade `src/compiler/35.semantics/any_escape/__init__.spl`
(`export use compiler.semantics.any_escape.checker.{AnyEscapeState,
any_escape_check, ...}`) and imported by
`src/compiler/80.driver/hir_semantic_consumer_v1.spl` as
`use compiler.semantics.any_escape.{AnyEscapeProfile, any_escape_check}`.

Reproduced on the unmodified seed (`origin/release/1.0.0` @ `81d3328925a`)
with no trait-dispatch change applied, so this defect is independent of the
CODEGEN-AMBIGUOUS-METHOD fix:

```
# in-tree probe: use compiler.driver.hir_semantic_consumer_v1.{collect_module_any_escape_receipt_v1}
SIMPLE_LIB=$W/src SIMPLE_NATIVE_BUILD_RUST_TRACE=1 simple run src/app/check/__jit_probe_any_escape.spl
[rust-jit] lowered functions=6807 externs=400
...
[rust-jit] compile functions done failed=0
[jit-fallback] unresolved external symbol 'any_escape_check': ...
```

## Bisection by import spelling (same binary, same tree)

| entry `use` | `[rust-jit] lowered functions=` | flattened? |
|---|---|---|
| `compiler.semantics.any_escape.{AnyEscapeProfile, any_escape_check}` (package facade) | **1** | **no** |
| `compiler.semantics.any_escape.checker.{any_escape_check}` | 2436 | yes |
| `compiler.semantics.any_escape.types.{AnyEscapeProfile, any_escape_kind_name}` | 27 | yes |

The facade import flattens NOTHING -- not even the `__init__.spl` -- while
both leaf imports flatten normally. So the `export use` chase, the
`load_matching_package_siblings` scan and the HIR/MIR side are not the
fault: the `use` never resolved to a path in the flattening loader at all.
The retained `UseStmt` was later resolved by the interpreter's own resolver
(which is why the fallback run prints the right answer), and HIR's
`import_loader` resolved the TYPE `AnyEscapeProfile` through
`module_resolver`, so the only thing missing from the JIT unit was the
function body -- exactly the "unresolved external symbol" shape.

## Root cause

`resolve_numbered_parts_from_root` (module_loader.rs:178-262) walks the
dotted path one segment at a time. For a NON-last segment it tries, in
order, the plain directory `<current>/<part>`, the layered alias, then a
numbered `NN.<part>` directory. For the LAST segment (`if is_last`,
line 185) it tries:

1. `<current>/<part>.spl`
2. layered alias dir -> `__init__.spl` / nested file
3. layered alias file
4. a numbered `NN.<part>/__init__.spl` or `NN.<part>/<part>.spl`

and then returns `None`. The plain package marker
`<current>/<part>/__init__.spl` is never tried when `<part>` is last.

For `compiler.semantics.any_escape` from root `src`: `compiler` is a plain
dir, `semantics` matches the numbered dir `35.semantics` (non-last branch,
correct), and `any_escape` is last: `35.semantics/any_escape.spl` does not
exist, there is no layered alias and no `NN.any_escape` dir, so the lookup
fails. The generic `resolve_parts_from_root` cannot rescue it either: its
dotted walk only knows `<name>.<segment>` directories (`compiler.semantics`),
not `NN.<segment>` ones, so it bails at `semantics`.

`compiler.semantics.any_escape.checker` works because `any_escape` is then
a NON-last segment and the plain-dir check runs.

## Why only this lane

The two sibling resolvers already check the plain package marker for the
last segment:

- interpreter: `interpreter_module/path_resolution.rs`
  `try_resolve_last_segment` (`.spl`, `.shs`, then
  `<dir>/<last>/__init__.spl`, then numbered) -- hence the correct output
  after the fallback;
- AOT / HIR import loader: `module_resolver/resolution.rs`
  `resolve_module_in_dir` (`.spl`, directory-is-the-module, then
  `<dir>/<last>/__init__.spl`, then `mod.spl`).

`native-build`'s object emission for every target goes through
`module_resolver`, so AOT output was never wrong; only the lane that
EXECUTES the compiler (`simple run` -> `pipeline::module_loader`) lost the
body and fell back to the interpreter.

## Fix

`resolve_numbered_parts_from_root`, `is_last` branch: after the same-named
`.spl` file check and before the layered-alias guesses, try the plain
package marker `<current>/<part>/__init__.spl` -- the exact probe the
non-last branch (`direct`) and both sibling resolvers already perform. Pure
`Path::join` / `p_is_file`, no separator string handling, so the behaviour
is identical on Windows, macOS, Linux, FreeBSD and SimpleOS hosts.

Ordering: a same-named file still wins (unchanged), and
`prefer_package_init_for_member_import` still promotes a `Group`/`Glob`
import of such a file to its package marker (unchanged). Only lookups that
previously returned `None` can now return a path, so no import that
resolved before resolves differently after.

## Evidence

Fixture: `test/fixtures/jit_facade_reexport_numbered_layer/src/{main.spl,
35.sem/pkg_a/__init__.spl, 35.sem/pkg_a/inner.spl}` -- the minimal
shape (facade whose last segment is a plain package dir under a numbered
layer, re-exporting an owner submodule's `pub fn`). It lives under a `src/`
directory because the interpreter's numbered-dir resolution is gated on
`/src/` in the base path.

Before (seed `81d3328925a`):

```
$ simple run test/fixtures/jit_facade_reexport_numbered_layer/src/main.spl
[jit-fallback] unresolved external symbol 'facade_f': whole module dropped to the interpreter ...
41
```

Spec `test/01_unit/compiler/jit_facade_reexport_numbered_layer_spec.spl`
(shells out with `SIMPLE_EXECUTION_MODE=jit`; oracle is the absence of the
`[jit-fallback]` marker): before `2 examples, 1 failure`; after
`2 examples, 0 failures`.

Rust unit test
`pipeline::module_loader::tests::numbered_layer_plain_package_init_resolves_and_flattens_facade_reexport`
(temp dir, same layout) fails before / passes after.

After: see the commit message on `work/jit-reexport-resolve-fable-20261030`
for the probe and cargo-test counts.

## Related

- `cranelift_jit_nested_fn_call_unresolved_external_symbol_2026-08-17.md`
  -- same error text, different mechanism (nested `fn` bodies not emitted).
- `entry_closure_drops_facade_reexport_owner_modules_2026-09-03.md` -- the
  Simple-written driver's phase-1 closure dropping facade owners; separate
  code, still open.
- `interpreter_use_unpack_reexports_transitive_closure_2026-10-20.md` --
  interpreter re-export table sharing; unrelated to resolution.
