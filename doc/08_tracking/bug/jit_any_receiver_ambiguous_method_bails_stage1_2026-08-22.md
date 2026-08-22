# JIT: a bare method on an `Any`/trait-object receiver bails the whole stage1 compiler

- **Filed:** 2026-08-22
- **Status:** PARTIALLY FIXED (seed, Rust) — 3 of 6 blocking bodies now JIT; see "Remaining"
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

## Remaining (stage1 is still NOT JIT)

The three `objtaker_*` bodies. Their candidates `SmfReaderImpl`
(`smf_reader.spl:278`) and `SmfReaderMemory`
(`_SmfReaderMemory/header_parser.spl:68`) are declared as bare `struct X:` and
are only DUCK-typed against the `SmfReader` trait — they declare no trait, so
they carry no vtable and there is no runtime identity to switch on. Two honest
options, neither taken here: declare the trait on the two structs (a
one-token pure-Simple change that reflects existing intent, not a JIT dodge),
or infer a vtable for a struct that structurally satisfies a trait used as a
parameter type (a language-semantics change; out of scope).

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
