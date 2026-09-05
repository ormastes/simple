# Rust interpreter rejects nested ClassInstance field assignment

**Status:** fixed; both focused Rust filters pass and the canonical Stage-2
compile-to-link cleared the blocker.
**Observed:** 2026-08-15.

## Symptom

After the Stage-2 unqualified `ChangeKind` source fix, a focused Rust-seed
native probe advanced to:

```text
error: semantic: invalid assignment: cannot assign field on non-object value
```

The diagnostic has no file, span, receiver, field, or runtime type. Evidence is
under `build/native_probe/stage2-field-assignment-20260815/`.

## Exact reproducer and boundary

The existing focused program is
`src/app/compile/test_dc_phase1.spl`. It constructs a `CompilerDriver`, prints
`Phase 1: loading...`, and calls `driver.load_sources_impl()`. With the admitted
Rust seed it reproducibly reaches the marker and then emits the same diagnostic:

```sh
src/compiler_rust/target/bootstrap/simple run \
  src/app/compile/test_dc_phase1.spl
```

`src/app/cli/bootstrap_probe_options.spl` passes (`backend=auto`), proving that
construction and direct field reads work. The failure begins inside
`CompilerDriver.load_sources_impl`; that method ends with the nested assignment
`self.ctx.sources = all_sources`.

This is decisively below the pure-Simple HIR/native boundary: the Rust AST
interpreter is executing valid Simple source. In
`src/compiler_rust/compiler/src/interpreter/node_exec.rs`, the two-level nested
field-assignment branch accepts only `Value::Object` for the outer receiver.
`self` in a method is a `Value::ClassInstance`, although the ordinary one-level
field-assignment branch already supports both `ClassInstance` and `Object`.
Consequently `self.ctx.sources = ...` falls into the generic non-object error.

## Required fix and coverage

Extend the two-level nested assignment owner to support a `ClassInstance`
outer receiver and an object/class-instance inner field, updating the inner
value through the instance field API. Do not convert instances to structural
objects or weaken the error.

Focused Rust coverage must include:

1. exact: `self.ctx.sources = value` where both `self` and `ctx` are class
   instances;
2. similar: class-instance outer receiver with a structural-object inner field;
3. negative: scalar inner field remains `INVALID_ASSIGNMENT` and preserves the
   original value.

The error context now attaches `assign.span` and `INVALID_ASSIGNMENT`, and
names the full receiver path, assigned field, and observed runtime type. That
diagnostic hardening makes future bootstrap failures attributable without a
3 GiB closure run.

The nested assignment branch now supports a class-instance outer receiver with
either a class-instance or structural-object inner field. It preserves the
outer binding on success and failure, attaches the assignment span, and retains
the scalar-inner rejection with the observed type in the diagnostic. The
negative test also asserts the exact code and span. Three focused Rust tests
cover the exact, similar, and negative cases.

Complete pre-fix interpreter stderr is retained at
`build/native_probe/stage2-field-assignment-20260815/mutation-probe.log`
(status 1). The separate larger loader trace is explicitly truncated by the
native-build entrypoint and is not substituted for the complete reproducer.

After the test scaffolding was aligned with the current interpreter API
(`ClassInstance` import, `Env::new` plus insertion, and a non-`Debug` error
match), both focused filters passed once:

- `nested_field_assignment_`: 3 passed, 0 failed.
- `nested_indexed_assignment_`: 3 passed, 0 failed.

The earlier combined-filter diagnostic assertion was corrected to require the
full receiver and an observed runtime type without hardcoding its display
spelling; code/span/nonmutation assertions remain. The three distinct
callable-ABI focused filters also passed. Manifest SHA-256
`cdb15cf755ee14ba561d6dede841ba077a848a6fca9e5ef46863beb456dc5586`
then verified all 27,070 covered files before authority publication. The
canonical transaction compiled all 846 Stage-2 entry-closure modules and
reached the final link without this assignment failure recurring.

Provider token usage and comparable completed-bug average: unavailable.

## Sibling gap found and fixed pre-emptively (2026-08-15, Claude partner session)

The INDEXED two-level shape has the identical ClassInstance hole and is the
very next line the reproducer path executes after this fix:
`driver_source_pipeline_loading.spl:63` — `self.ctx.modules[module_name] = …`.
In `node_exec.rs`'s Index-target Case 2 nested branch
("obj.field1.field2[index] = value"), the root matched ONLY `Value::Object`;
a `ClassInstance` root (`self`) fell through to
"nested field access not fully supported". The driver pipeline uses this shape
at 8+ sites (`driver_pipeline_lowering.spl`, `driver_pipeline_passes.spl`,
`driver_pipeline_aop.spl`), so without this the probe advances exactly one
statement.

Fix mirrors the plain-nested ClassInstance support: a `ClassInstance` root is
read via `env.get` (no remove/re-insert needed); a class inner mutates the
shared instance's container field via `field`/`set_field`; a struct inner is
copy-on-write and written back to the root instance; Array grow-on-append and
Dict `wrap_dict_entry` semantics are byte-identical to the Object-root path;
a non-container field errors without mutating. A three-level plain sweep of
`src/compiler`/`src/app` found zero sites, so no deeper shape is needed.

Tests added beside the plain-shape ones in `node_exec.rs`:
`nested_indexed_assignment_supports_class_instance_root_and_inner` (exact
driver shape), `nested_indexed_assignment_supports_struct_inner_array`, and
`nested_indexed_assignment_rejects_scalar_container_without_mutation`.

Known remaining (deliberately unfixed, no known call site): an `Object` root
with a `ClassInstance` inner in either two-level shape still errors.

Completed verification command (with the plain-shape tests):

```sh
cargo test --release -p simple-compiler nested_ \
  --manifest-path src/compiler_rust/Cargo.toml
```

## Third suspected sibling ruled out by live probe (2026-08-15, Claude partner session)

The workaround comment in `load_sources_impl` ("self.ctx.sources.push()
doesn't persist — interpreter limitation") suggested nested-field METHOD
mutation was a third hole. It is NOT: `handle_method_call_with_self_update`
ends in a general place-resolver fallback (`interpreter/place.rs` —
`resolve_place`/`store_path`), and that path fully supports ClassInstance
roots, ClassInstance inners (shared-identity `set_field`), and struct inners
(copy-on-write). Verified live on the admitted seed with two T0 probes:
class-in-class `self.ctx.warnings.push(w)` and struct-in-class
`self.config.libraries.push(p)` both persist (`count=2` / `libs=2`).
The `load_sources_impl` comment is STALE — it predates the place fallback.
A redundant interception branch briefly added for this suspicion was removed
after the probes; `interpreter_helpers/patterns.rs` is unchanged from HEAD.
The `driver_pipeline_aop.spl` / `object_provider.spl` push sites need no fix.

## Reproduction boundary pinned by probe bisection (2026-08-15, Claude partner session)

Nine live probes on the pre-fix seed produced an apparent contradiction and
then resolved it:

- Standalone fixtures of every representation combo (class/struct inner,
  literal/static-factory construction, single- and cross-module) all PASS
  `self.ctx.sources = …`.
- The real reproducer, a minimal `d.ctx.sources = []` after
  `CompilerDriver.create`, a probe-local holder class wrapping the real
  `CompileContext`, and finally a PURE synthetic (probe-local `MyOuter` /
  `MyInner`, no compiler values at all) with a single
  `use compiler.common.driver_core_types.{CompileOptions}` import all FAIL
  with the same `cannot assign field on non-object value`.
- One-level assignment on the same values (`d2.ctx = ctx2`,
  `x = d2.ctx; x.sources = []`) always PASSES.

Conclusion: the failure is selected by the EXECUTION ENVIRONMENT, not the
value shape. `driver_core_types.spl` itself has zero imports; naming any
`compiler.*` module pulls the multi-module co-compiled closure, and in that
mode function bodies execute through the `node_exec::exec_assignment` nested
branch — which, pre-fix, had no ClassInstance-root arm and errors. In the
light single-module mode the same statement takes a different executor path
(place-fallback capable) and succeeds, which is why every small fixture
passed and why unit-style fixtures CANNOT gate this fix.

Consequences:
1. The ClassInstance parity fix in `node_exec.rs` (plain + indexed arms) is
   confirmed as addressing the real Stage-2 blocker path.
2. The honest post-rebuild gate is the HEAVY environment, not a unit fixture.
   The manifest-verified canonical Stage-2 run compiled all 846 entry-closure
   modules and reached final link without this assignment failure. The
   standalone `test_dc_phase1` runner remains useful only for executor-path
   parity; the retained probe series under
   `build/native_probe/stage2-field-assignment-20260815/probes/` (steps A–N)
   provides finer-grained localization if that separate follow-up regresses.
3. Open follow-up (separate lane, not blocking): the interpreter executes
   the same assignment statement through two different code paths depending
   on whether the module graph is co-compiled; the light path is
   place-capable and the heavy path was not. Unifying them on the place
   fallback would remove this class of environment-dependent bugs wholesale.

## Historical ahead-of-rebuild probe sweep (2026-08-15)

Probed the pipeline chain BEYOND the blocked assignment with the pre-fix seed
(`src/compiler_rust/target/bootstrap/simple`), heavy environment, probes under
`build/native_probe/stage2-field-assignment-20260815/probes/`:

- `pff_heavy.spl` — `CompileOptions.default()` + `CompileContext.create(opts)` +
  `parse_full_frontend(src, …, ctx.logger)` on a real two-function source: **PASSES**
  (`S1`/`S2` printed). Also pass: `pff_lite.spl` (minimal `Logger.from_env()`),
  `pbm.spl` (`parse_and_build_module_scoped` direct), `lexinit.spl`
  (`lex_init`/`lex_source_len`, exercising the `current_core_lexer` module global).
- An earlier apparent failure (`variable current_core_lexer not found`) was an
  ARTIFACT of running the probe from a directory outside the repo: `compiler.*`
  imports do not resolve there and the module loads partially. **Probe caveat for
  future sessions: heavy-env probes MUST live inside the repo tree.**
- Honest gate re-run (`simple run src/app/compile/test_dc_phase1.spl`) still fails
  with exactly `semantic: invalid assignment: cannot assign field on non-object
  value` right after "Phase 1: loading..." — no earlier regression has crept in;
  this was pre-rebuild evidence. The corrected seed and subsequent canonical
  846/846 compile-to-link run later cleared this blocker.
