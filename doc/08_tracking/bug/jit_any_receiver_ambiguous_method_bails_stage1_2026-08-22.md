# JIT: a bare method on an `Any`/trait-object receiver bails the whole stage1 compiler

- **Filed:** 2026-08-22
- **Status:** FIXED — all 6 blocking bodies now JIT (`[CODEGEN-AMBIGUOUS-METHOD]` sites 18 → 0). Stage1 still de-JITs, but on a DIFFERENT single cause; see "Next gate".
- **Severity:** High (perf) — stage1 `compile` still runs 100% on the tree-walker
- **Component:** Rust seed JIT — `src/compiler_rust/compiler/src/codegen/{instr/closures_structs.rs,instr/mod.rs,closure_boxed_entry.rs,common_backend.rs}`, `hir/lower/module_lowering/module_pass.rs`, `parser/src/types_def/mod.rs`
- **Parent record:** `jit_fn_ref_port_bails_whole_stage1_2026-08-22.md` (landed 7a137dbffdb)

## Symptom

With the fn-ref bail gone, Cranelift compiles the stage1 closure but 6 bodies
still fail, which fails the whole module:

    [CODEGEN-AMBIGUOUS-METHOD] in 'BlockRegistry.register' bare method 'kind'
    has 6 candidates: [JsonDef.kind, ShellDef.kind, SqlDef.kind, ...]
    — refusing to pick shortest (would silently miscall)
    [INFO] JIT compilation failed, falling back to interpreter: ...
    codegen: 6 function body/bodies failed to compile

The six: `BlockRegistry.register` / `register_block` / `with_block`
(`src/compiler/15.blocks/blocks/registry.spl`, `block_def: Any` ->
`block_def.kind()`) and `objtaker_take_object` / `_with_types` / `_concrete`
(`src/compiler/70.backend/linker/obj_taker.spl`, `smf_reader: SmfReader`).

## Root cause

Codegen binds a bare (dot-less) method by NAME SUFFIX alone. With several
`Type_dot_<method>` symbols linked in it cannot tell them apart, so it
correctly refuses rather than miscall — but it had no runtime discriminator to
fall back on. It does in fact have one: a struct implementing a trait carries
that trait's vtable pointer at offset 0 (`compile_struct_init`, keyed on
`vtable_data_ids`), and that pointer is a per-struct constant address, i.e. a
runtime type identity.

## Fix (seed, semantics-preserving; no pure-Simple call site rewritten)

1. `closures_structs.rs::try_emit_vtable_type_switch` — when every candidate's
   owner carries a vtable, emit a runtime type switch on the receiver's vtable
   word: `vt == &__vtable__A -> A.method(recv, args)`, ... , else
   `rt_method_not_found` (which aborts, as the interpreter does). Nothing is
   guessed: an unlisted receiver type aborts rather than reaching a wrong
   candidate; two candidates sharing one vtable refuse, keeping the old bail.
2. `module_pass.rs` + `parser/types_def/mod.rs` — `struct Name(Trait):` was
   parsed and then DISCARDED (`if let Some(_trait_name) = implements_trait`),
   so such structs got no `HirImpl`, no vtable, and no trait identity at all.
   The parser now carries the trait as a synthetic `implements(Trait)`
   attribute and HIR records the impl exactly as an `impl Trait for Name`
   block would (default methods included).
3. `instr/mod.rs` `AggregateCopy` — **soundness bug found on the way.** A
   by-value copy of a vtable-bearing struct sized itself from the field layout
   only, so it copied ONLY the 8-byte vtable header and every field read
   through the copy answered 0 (`self.base + n` == `n`). Now shifted +8 with
   deep-field word indices rebased, mirroring StructInit/FieldGet.
4. `closure_boxed_entry.rs::emit_vtable_selfless_entries` — **second soundness
   bug.** HIR drops the `self` parameter from a method body that never uses
   it, but a virtual call always passes the receiver first, so such a slot read
   the object as its first user argument (measured: a fieldless
   `FileReader.lookup(n)` answered 999 for n=4). Each such slot now points at a
   `name$vt` thunk that accepts and drops the receiver.

## Evidence

- `src/compiler_rust/compiler/tests/any_receiver_vtable_dispatch_jit.rs` —
  `compile_module` must return Ok and the calls must answer correctly, for an
  `Any` receiver over 3 implementors and for a trait-typed parameter over 2.
  Both FAIL pre-fix (Err, `[CODEGEN-AMBIGUOUS-METHOD]`), green post-fix.
- Fixtures `test/01_unit/compiler/jit_dyn_dispatch/f0{1,2}*.spl` — pre-fix both
  de-JITted; post-fix both JIT and every value is correct. `f02` is
  byte-identical to the interpreter. `f01` DIVERGES, and the JIT is the correct
  side: for a free `fn describe(block_def: Any) -> text` returning
  `block_def.kind()`, the JIT answers `sql` while the INTERPRETER answers
  `unnamed` / `nil` and additionally prints a spurious `0 examples, 0 failures`
  banner. That is a separate pre-existing interpreter defect on erased-receiver
  free functions, unrelated to this change and not fixed here; it is recorded
  so the divergence is not later misread as a JIT miscompile.
- Perf gate: `scripts/check/check-perf-regression-tests.shs` rows `ANYVTJIT`
  (PASS — 74 mechanisms checked).
- Stage1 entry (`bootstrap_main.spl compile hello.spl --format=smf`):
  6 failing bodies / 18 ambiguous sites -> **3 failing bodies**, the three
  `BlockRegistry` ones now compile. Wall is not a valid before/after yet
  (both runs still de-JIT; measured 228 s pre-fix vs 188 s post-fix on a
  loaded box — that spread is load, not this change).

## Resolved: the duck-typed half

`objtaker_take_object/_with_types/_concrete` take `smf_reader: SmfReader`, but
the concrete type flowing in, `SmfReaderImpl`, declared its methods in a bare
`impl SmfReaderImpl:` block — so it had no trait impl, no vtable, and no runtime
identity, and the call fell back to ambiguous bare-name binding. Changed to
`impl SmfReader for SmfReaderImpl:` (plus importing the trait). That is
declaring intent that already existed — the struct's own comment says "implements
SmfReader trait" and it implements all 5 methods — not a rewrite of any call
site. MIR lowering then finds the trait and emits a proper `MethodCallVirtual`
slot dispatch, which is the pre-existing correct path.

**`SmfReaderMemory` was deliberately NOT declared.** It implements only 2 of the
trait's 5 methods (`lookup_symbol`, `read_code`; missing `path`,
`read_template_section`, `read_note_sdn`). Declaring the trait on it would be
false, and would emit a vtable with three ZERO slots — `compile_method_call_virtual`
loads the slot and calls it, so any dispatch through those would be a NULL jump.
It is safe to leave undeclared because it is never passed as an `SmfReader`:
its only users (`99.loader/loader/module_loader_lib_support.spl`,
`70.backend/linker/smf_getter.spl`) hold it by concrete type. If it ever needs
to flow through the trait, the three missing methods must be IMPLEMENTED first,
not merely declared.

## Next gate (stage1 still de-JITs, for a different reason)

With the ambiguity gone the module reaches the NEXT guard and stops there:

    [jit-fallback] unresolved external symbol 'rt_process_read_stdout_checked':
    whole module dropped to the interpreter (expect ~100-1000x slowdown)

That is `first_unresolved_import` (`jit.rs`), a separate defect class: one
runtime symbol the JIT cannot resolve. It is now the single named blocker
between stage1 and a JIT-compiled run, and it is far more tractable than the
dispatch problem was.

## Where stage1's wall actually goes (redirects the next profiling lane)

`SIMPLE_INTERP_SAMPLE=1` on the stage1 `compile` run: **3561 total samples,
3460 idle — only ~101 samples (2.8%) have a Simple frame at all.** The
tree-walking interpreter is therefore NOT where stage1's wall time goes; ~97%
is seed-native work (module loading, HIR/MIR lowering, codegen). This matters
for planning: it means getting stage1 to JIT will NOT by itself deliver the
~30x that the per-statement interpreter cost suggests, and the next profiling
lane should target the seed's native phases rather than the interpreter loop.

## Why per-function deopt (the more general fix) was NOT taken

Falling back only the FAILING function to the interpreter, leaving the rest
JIT-compiled, is blocked twice over on the current architecture:
- The JIT `run` lane never calls `init_interpreter_state`, so the
  `rt_interp_call` bridge has an EMPTY function table; every deopted call
  would resolve to nothing and return NIL (a silent wrong answer, the exact
  defect class `SIMPLE_NO_STUB_FALLBACK` exists to prevent).
- `value_bridge.rs` reconstructs `bridge_tags::OBJECT` as
  `Value::Object { fields: Arc::new(HashMap::new()) }` — a struct crossing the
  bridge LOSES ALL ITS FIELDS. Every one of these bodies takes a struct
  receiver, so the bridge cannot carry them even if the table were seeded.
Making deopt real means seeding interpreter definitions on the JIT lane and
giving the bridge a lossless struct representation. Filed here as the next
lever rather than half-built.
