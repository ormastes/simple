# JIT trait dispatch and cross-module linking (caret fallback chain)

Status: DESIGN, phase 1. Not implemented. Date: 2026-11-13.
Base: `origin/release/1.0.0` at `fe75b13a584`. Seed built from that base with
`CARGO_TARGET_DIR=/home/yoon/dev/.cargo-target-jit-dispatch-20261113`
(sha256 prefix `a64ac53aaf6ca014`; a clean rebuild after reverting the
diagnostic patches reproduced the same hash).

## Goal

`SIMPLE_RUST_SEED_WARNING=0 <seed> run src/app/llm_caret/main.spl --help` must
run under the Cranelift JIT, with no `JIT compilation failed` line and no
whole-module `engine-demotion`. One `engine-demotion reason=hybrid-interp-splice`
line (row 5) will remain after this lane. It is a partial demotion and is out
of scope here, which is an owner decision. The steps below do not remove it. The user asked for two candidate mechanisms:

- **Option A:** a run-time by-name method dispatch thunk, used when the
  receiver's type is a trait or `ANY`;
- **Option B:** cross-module JIT linking of imported Simple functions.

This document lists the actual fallback chain first, because the chain decides
which option is needed.

## 1. Current fallback chain (measured)

The JIT reports only ONE whole-module failure per run.
`compile_all_functions` collects every body failure. Then
`first_unresolved_import_called` (`codegen/jit.rs:500`) returns on the
first unresolved import. So a body failure hides every import failure behind
it. To see the whole chain I ran three diagnostic builds. Each was reverted
afterwards and none is committed:

- `SIMPLE_ALLOW_STUB_FALLBACK=1` gets past the body failure.
- A temporary `continue` in `first_unresolved_import_called` lists every
  unresolved import instead of only the first.
- A temporary env-gated change to the `ExportUseStmt` branch of
  `load_module_with_imports_internal` (`pipeline/module_loader.rs:2577`) tests
  the loader hypothesis for rows 2-4.

| # | Layer | Symbol / site | Cause class | Provenance |
|---|---|---|---|---|
| 1 | codegen body (`[CODEGEN-AMBIGUOUS-METHOD]`) | `_pure_database_select_owned_v1`: `strategy.provider_identity()` (and the 4 sibling calls after it in the same body) | **HIR trait-owner propagation gap.** `val strategy = slot.reducer` is an unannotated local initialised from a trait-typed FIELD read. `declared_local_trait_owner` (`hir/lower/stmt_lowering.rs:321`) only handles `Call`/`MethodCall` initialisers, so the local gets no `trait_dispatch_owner`. MIR then takes the impl-less duck path and emits a bare `provider_identity`. Codegen finds 6 unrelated same-named candidates and refuses. | origin binary, run1 |
| 2 | unresolved import | `smux_runtime_binding_bind_v3` | **Loader flatten-parity gap.** It arrives only through `pub use os.apps.smux.runtime_binding_bind_v3.smux_runtime_binding_bind_v3` in `runtime_binding_owner_v3.spl`. The `ExportUseStmt` branch decides flattening with `should_flatten_nested_import` alone. The `UseStmt` branch (`:2516`) also ORs `single_import_targets_module_file`. So a single-symbol `pub use` of a module file is loaded but never flattened, and the body never reaches MIR (`mir_functions=[]` in the `SIMPLE_JIT_SYMBOL_TRACE` record). | diagnostic build (stub fallback + list-all), run2/run3 |
| 3 | unresolved import | `smux_runtime_binding_prepare_v3` | same as 2 | run2 |
| 4 | unresolved import | `smux_runtime_binding_inspect_v3` | same as 2 | run2 |
| 5 | partial demotion `hybrid-interp-splice` | 392 extern names | **Not a module drop.** These are extern declarations with no JIT-resolvable runtime symbol. `run_file_jit` rewrites each call into an `InterpCall` bridge to the interpreter extern table (`driver/src/exec_core.rs` ~1290), and the rest of the module stays JIT-compiled. Breakdown: ~70 are platform-foreign (32 Win32 such as `GetTickCount64`/`DeleteProcThread…`, plus kqueue, iocp, event_ports, arm, port I/O) and can never be host symbols here. The remainder are host-applicable `rt_*` that are not registered in the JIT symbol provider (76 `rt_process_*`, 57 `rt_simd_*`, 25 `rt_linux_*`, 23 `rt_http_*`, 18 `rt_local_*`, ...). | origin binary, run1 |

Notes on provenance:

- In run2 the `jit-panic` (`can't resolve symbol smux_runtime_binding_inspect_v3`)
  comes from my diagnostic `continue`, which let finalize meet the NULL import.
  It is not a real fallback.
- With the loader parity change active (run4), **zero** unresolved imports
  remained. Caret `--help` finished under the JIT, and the only failure left was
  the stubbed row 1. Run4 also showed no new `co-compiled definitions` warnings
  (82 before and 82 after), so flattening the extra modules adds no new
  duplicate-symbol ambiguity on this path.
- Scope limit: only the `--help` path was measured. Other caret modes
  (`--server`, providers, GUI) may reach code that this path never executes.
  Compile-time rows (1-4) cover the whole flattened unit regardless of mode.
  Run-time miscompiles do not.
- Historical rows already fixed on this base:
  - `daemon_read_frame_v1` and `bounded_frame_limit_v1` were missing files,
    fixed in `80a86e7df15`.
  - The unbraced single-symbol `use` was a loader gap, fixed in `10d459a857f`.
  - Row 2's class is the `pub use` twin of `10d459a857f`.

### Row 1 reduced to 30 lines

The repro is a scratch file, not committed. Its shape becomes the step-1 test
below. It contains a trait `Reducer`, two unrelated classes `A`/`B` that each
have `ident()`, a `class Slot: r: Reducer`, and no conformer anywhere.

- `fn via_param(r: Reducer): r.ident()` lowers as `virtual trait call at slot 0`
  and compiles.
- `if val Some(s) = slot: val x = s.r; x.ident()` lowers as a bare `ident`.
  Codegen reports `[CODEGEN-AMBIGUOUS-METHOD]` with 4 candidates and the whole
  module drops to the interpreter.

The `Some(s)` binding is already typed `Struct Slot`, so the existing
`trait_field_dispatch(base, field)` helper already resolves `s.r` to `Reducer`.
Only the `let` initialiser arm is missing.

The same file shows that a trait-typed parameter in a unit with **zero
conformers** already compiles to `MethodCallVirtual`
(`pure_database.spl:1843-1847`, same five methods, same unit). So row 1 needs
no run-time by-name dispatch. It needs the same owner identity that a
parameter already gets.

### Two more findings from executing the vtable path

Both were measured on the origin binary.

**(a) A structural conformer crashes the existing vtable path.**
- An annotated local `val x: Reducer = s.r` emulates the proposed step 1 with
  no seed change. Under the JIT, the whole module JIT-compiled.
- With `class C with Reducer` behind it, `x.ident() + "{x.bits()}"` printed
  `c7`, which is correct.
- With `class D` (same methods, no `with`) behind it, the run hit **SIGSEGV
  (rc 139)**. D has no vtable word, so `MethodCallVirtual` loads field 0 as a
  vtable pointer.
- This is a pre-existing crash. It is reachable today through any trait-typed
  parameter or annotated local that holds a duck-conforming object. It must be
  filed as a bug.
- Consequence: step 1 must not route a site to `MethodCallVirtual` unless every
  class in the unit that could be coerced to the trait carries the trait vtable.
  Two ways to meet that rule:
  - give every structural conformer a vtable at the coercion site;
  - refuse vtable dispatch when a structural conformer exists in the unit, and
    keep the #8683 bind/refusal for those sites.
- For caret this is safe either way, because the unit has zero conformers of
  any kind.

**(b) A second, caret-specific gap.**
- Annotating the caret site itself (`val strategy: PureDatabaseBitmapReducerV1
  = slot.reducer`, applied temporarily and reverted) did **not** remove row 1.
- In the same run, `SIMPLE_DEBUG_METHOD_DISPATCH=1` showed:
  - the `query_with_bitmap_reducer_owned_v1` parameter site lowered as
    `virtual trait call at slot 0`;
  - the annotated local in the free function `_pure_database_select_owned_v1`
    still lowered bare (`receiver ty = Any (local-table fallback also
    unnamed)`).
- The same shape compiles virtual in a standalone file, including the call
  placed inside a constructor's named argument.
- So inside the flattened caret unit, `declared_trait_dispatch` /
  `trait_declaration_for_current_owner` fails for this free function. One
  hypothesis is that owner resolution differs for free functions versus class
  methods in the flattened unit, or that the trait name is co-registered under
  more than one owner. That needs tracing before step 1 is built. The
  `FieldAccess` arm alone is necessary but **not sufficient** for caret.

## 2. Object identity facts both options depend on

These facts constrain A, and they constrain how A and B interact:

1. **A JIT-constructed class instance is a bare `rt_alloc` block**
   (`codegen/instr/closures_structs.rs:562` `compile_struct_init`). It has no
   `HeapHeader` and no class id. A class that implements a trait gets an 8-byte
   vtable pointer at offset 0, keyed on `ctx.vtable_data_ids`. All other
   classes start directly with field 0.
2. **An interpreter-bridged object is a `RuntimeObject`** (`rt_object_new`,
   `runtime_bridge.rs:319`). It has a `HeapHeader` and a registered class id.
   That layout differs from (1). `Value::TraitObject` marshals to `NIL`
   (`runtime_bridge.rs:154`).
3. **`runtime_to_value` reads a `HeapHeader` from every heap pointer.** A raw JIT
   struct pointer passed to it therefore has its vtable word or first field
   misread as a header.
4. **Under `run`, the JIT unit is the whole program.** `load_module_with_imports`
   flattens the import closure into one unit. The only interpreter round-trips
   in a successful JIT run are `InterpCall` bridges to *externs* (row 5).
   Externs return extern values, not Simple class instances. **So today no
   object of a class outside the unit can reach JIT code.** "Out-of-unit
   implementor" becomes possible only after B-proper (section 4) or per-function
   hybrid interpretation exists.

## 3. Option A — run-time by-name method dispatch thunk

### Shape

A new MIR form (or a new miss arm on the existing vtable type switch,
`try_emit_vtable_type_switch`, `closures_structs.rs:3038`):

```text
r = rt_method_dispatch(recv, "provider_identity", argc, argv)
```

The runtime would need a process-wide table mapping (receiver runtime type,
method name) to a code pointer. Every compiled unit would register its
methods in that table at finalize. Each object kind would be handled as
follows:

- **`RuntimeObject` (has a class id):** look up `Class.method` in the table.
  If the table has no entry, call the interpreter via
  `rt_interp_call("Class.method", ...)`.
- **JIT struct with a vtable header:** the vtable pointer identifies the
  class. Map it to the class name through a vtable-pointer → class registry,
  then use the same table.
- **JIT struct with no vtable header:** there is **no runtime identity**.
  The thunk cannot dispatch these at all. Supporting them would mean adding a
  type header to every JIT object. That changes field offsets for every class
  and every FieldGet/FieldSet/copy site, and it breaks the 8-byte header
  invariants already pinned in `emit_aggregate_block_copy`.

### What A removes from the chain

- **Row 1:** only by accident. The receiver is statically a trait, and the
  vtable path already works there. A would route a statically-known trait call
  through a slower, string-keyed path.
- **Rows 2-5:** none of them.

### Interaction with B

If B-proper lands, an implementor class can be compiled in another unit.
Objects of that class are built by that unit's `compile_struct_init` and carry
that unit's vtable pointer. Vtable-slot dispatch (`MethodCallVirtual`) handles
this correctly **only if** both units agree on the trait's slot order. Slot
order comes from the trait declaration, so they agree when the trait itself is
shared. A by-name thunk is needed only for receivers that are `ANY`, or duck
traits with no `with`. Those objects carry no vtable, so (1) applies and the
thunk has nothing to key on.

**Conclusion:** A is the right tool only for `RuntimeObject` receivers, which
appear once the JIT and the interpreter exchange Simple objects. Nothing in the
current chain needs it.

### Cost and risk

- New runtime table, registration at finalize, a vtable → class registry,
  argument marshalling, and boxed-return handling, which repeats the
  `InterpCall` composite-return gaps (`mir/hybrid.rs` S68/S71 notes).
- High risk of a **silent wrong value**: a thunk that reaches
  `runtime_to_value` with a raw JIT struct gets garbage, not an error (fact 3).
- Must fail closed. A miss must call `rt_method_not_found`, which aborts like
  the interpreter. It must never return `NIL`.

### Tests A would need

- A JIT `RuntimeObject` receiver dispatching to a JIT-compiled method and to an
  interpreted method.
- A vtable-header receiver routed by the vtable → class registry.
- A no-header receiver that refuses at compile time instead of dispatching.
- Miss → `rt_method_not_found` abort (exit code and message pinned).
- Composite returns (`text`, tuple, `Result`) across the thunk.
- Negative: an `ANY` receiver holding an array or text must not match a class
  method.

## 4. Option B — cross-module JIT linking

Two different things share the name "cross-module".

### B-lite: flatten parity in the module loader (what caret needs)

The `UseStmt` branch flattens a single-symbol import of a module file through
`single_import_targets_module_file` (`module_loader.rs:908`). This predicate
predates `10d459a857f`, which touched the same loader for the unbraced `use`
binding case. The `ExportUseStmt` (`pub use`, `:2577`), `CommonUseStmt`
(`:2628`) and `MultiUse` (`:2681`) branches do not. Give all four the same
predicate, preferably through one shared helper so the four sites cannot drift
apart again.

- **Removes:** rows 2-4. Verified by the run4 diagnostic: zero unresolved
  imports afterwards.
- **Cost:** about 10 lines in the seed.
- **Risk:**
  - More modules are flattened, which adds compile time and can add
    duplicate-definition ambiguity. On caret `--help` this was measured at
    82 → 82 `co-compiled` warnings and no new `[CODEGEN-AMBIGUOUS-METHOD]`.
  - The interpreter path is unaffected, because the flattened copy is only an
    addition.
  - `CommonUseStmt` and `MultiUse` were not exercised by caret. They need their
    own fixture tests.
  - The predicate exempts only a target that resolves to `__init__.spl`. A
    `pub use a.b.f` line inside an aggregator file that is *not* named
    `__init__.spl` would now flatten every sibling module it names. That can
    widen the unit and bring in same-named private helpers. A fixture must cover
    a non-`__init__` aggregator that re-exports two siblings defining the same
    private helper name.

### B-proper: separate JIT units plus symbol linking

Each module would be compiled as its own `JITModule` unit, with each import
resolved against a process-wide registry of finalized units through a
`JITBuilder::symbol_lookup_fn`. That needs:

- a stable mangling shared by units;
- an import-before-export order, or lazy stubs, for cycles;
- vtable data that crosses units (`vtable_symbol` already exists on `MirInst`
  for native-project qualification);
- per-unit global stores (`module_globals_generation` style).

- **Removes:** nothing that B-lite does not already remove for caret, because
  under `run` everything is flattened (fact 4).
- **Pays off:** for incremental JIT and REPL/LSP hot reload, and for
  compile-time scaling of very large flattened units.
- **Cost:** large, weeks. **Risk:** high. Cross-unit vtable layout agreement is
  the main source of silent wrong dispatch.
- **Interaction:** this is the change that makes "an out-of-unit implementor
  reaches the call" real. Before B-proper ships, it needs:
  - a cross-unit vtable test (implementor in unit X, `MethodCallVirtual` site
    in unit Y);
  - the A thunk, or a compile-time refusal, for `ANY` receivers that may hold
    unit-X objects.

### Tests B needs

- **B-lite:**
  - one fixture per branch (`pub use a.b.f`, `common use`, multi-use) whose
    body is only reachable through that form;
  - each fixture runs under the JIT with no `jit-fallback` line and returns the
    right value;
  - a negative fixture: a package `__init__.spl` aggregator stays lazy, as
    `single_import_targets_module_file` already requires.
- **B-proper:**
  - cross-unit call, cross-unit vtable dispatch, a cycle between two units,
    reload of one unit, and a global defined in unit X written from unit Y.

## 5. What each option removes

| Row | Option A | B-lite | B-proper | Owner-propagation fix (step 1) |
|---|---|---|---|---|
| 1 `_pure_database_select_owned_v1` | incidental, slower, wrong layer | no | no | **yes** |
| 2-4 smux `*_v3` | no | **yes** | yes, overkill | no |
| 5 hybrid splice (392 externs) | no | no | no | no |

Row 5 belongs to a third track: JIT symbol-provider registration for
host-applicable `rt_*`, plus cfg-pruning of platform-foreign externs from
host units. Neither A nor B touches it. It is a partial demotion, not a module
drop.

## 6. Recommendation and step plan

**Recommendation: build neither A nor B-proper now.** Remove caret's
module-drop chain with two narrow seed fixes that reuse machinery that already
exists. Keep A and B-proper as recorded designs, gated on the event that makes
them necessary: JIT/interpreter object exchange for A, separate JIT units for
B-proper.

Each step is TDD: write the failing spec or test first, make the change, then
record red-to-green evidence.

1. **Trait owner for field-initialised locals (row 1).**
   - **1a. Locate gap (b) first.** Trace `declared_trait_dispatch` for the
     annotated caret local, and land whatever owner-resolution fix it needs.
     Use a fixture that reproduces gap (b) outside caret: a free function in a
     module imported through a `pure_sql.database`-style package.
   - **1b.** Add an `Expr::FieldAccess { receiver: Identifier, field }` arm to
     `declared_local_trait_owner` that returns
     `self.trait_field_dispatch(base, field, ctx)`.
   - **1c. Structural-conformer guard.** Apply it as defined in finding (a),
     and file the SIGSEGV as a bug.
   - Tests:
     - Extend `hir/lower/tests/trait_field_receiver_tests.rs` with
       `val s = self.store; s.read(k)` and the
       `if val Some(slot) = opt: val x = slot.r; x.m()` shape. Assert
       `MethodCallVirtual`, and assert that no bare `MethodCallStatic` is
       emitted.
     - JIT behaviour runs:
       - a nominal conformer gives the right value (`c7`);
       - a structural conformer gives a clean compile-time refusal or the right
         value, never SIGSEGV;
       - zero conformers compiles, and the call is never reached.
     - Each behaviour run must print no `JIT compilation failed` line, so the
       value is known to come from the JIT.
2. **Loader flatten parity (rows 2-4).**
   - Extract one predicate and use it in all four branches of
     `load_module_with_imports_internal`.
   - Tests: the B-lite fixtures listed in section 4.
3. **List every unresolved import, not the first.**
   - `first_unresolved_import_called` should collect all names into the
     `[jit-fallback]` message, keeping the same fail-closed `Err`, so the next
     chain is visible in one run.
   - This is diagnostic only and has no policy change.
4. **Re-measure caret.** Run `--help` on the origin rebuild, then one
   `--server` / provider path. Expect: no `JIT compilation failed`, only the
   row-5 splice.
   - Record timing and peak RSS before and after, with the binary identity
     (sha256), as the three-axis acceptance rule requires.
   - Strip the env-gated diagnostics before landing.
5. **File row 5 as its own todo:** register host `rt_*` symbols in the JIT
   provider, and cfg-prune foreign externs. This is not part of this lane.
6. **A and B-proper:** no code. This document is the record. Revisit A when a
   lane needs JIT ↔ interpreter Simple-object exchange (per-function hybrid).
   Revisit B-proper when incremental JIT or hot reload is planned. Section 4
   lists the cross-unit vtable test that must come first.
