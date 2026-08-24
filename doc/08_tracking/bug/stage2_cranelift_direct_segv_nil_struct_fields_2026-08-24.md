# Stage-2 SEGV: unguarded deref of nil struct fields in stage2-generated code (2026-08-24)

Status: OPEN — root cause narrowed, not yet fixed.
Lane: S. Binary under test (frozen, do not modify):
`/mnt/data/worktrees/goal-bootstrap-frozen/build/bootstrap/goal-r4/stage2/x86_64-unknown-linux-gnu/simple`

## Reproduce (deterministic, sub-second)

```
printf 'fn main()\n    print("hi")\n' > h2.spl
<stage2> compile h2.spl --format=smf -o h2.smf ; rc=$?   # rc=139
```
Last stdout markers: `[cranelift-direct] start` / `target` / `module`.
NOTE: a fixture using `fun main()` does NOT reach the backend (HIR error
`unresolved name: fun`) — the crash needs `fn`.

## Backtrace A — this lane's crash (backend, post-MIR)

```
#0 0x8fb7dd compiler.backend.backend.cranelift_codegen_adapter.build_signature
#1 0x8faa85 ...cranelift_compile_module_direct
#2 0x8efc2a backend_helpers.compile_module_with_backend_target_cpu_storage_bindings
#3 0xa888f1 driver_aot_smf_output.CompilerDriver.collect_smf_bytes
#4 0xa8836a driver_aot_smf_output.CompilerDriver.compile_to_smf
#5 0x49ebe4 app.cli.bootstrap_main.run_compile_bootstrap
```

Faulting instruction (`build_signature+0x19d`):
```
8fb7d5: mov 0x8(%rbx),%rax     # sig.return_type
8fb7d9: and $0xfffffffffffffff8,%rax
8fb7dd: mov (%rax),%r15        # <-- rax == 0, SEGV. no nil guard
```

## Field-level evidence (gdb, breakpoint at the declare loop)

`module.functions` has exactly 1 entry (NFUNCS=1) and the dict lookup works.
The stored `MirFunction` (base 0x7288a40) reads:

| off | field (mir_instruction_graph.spl:159) | value |
|-----|---------------------------------------|-------|
| +0x00 | symbol: SymbolId    | 0x72888b1  (ptr, live) |
| +0x08 | name: text          | **0x3 = nil** |
| +0x10 | signature: MirSignature | 0x72888d1 -> {0,0,0} all fields zero |
| +0x18 | locals: [MirLocal]  | **0x3 = nil** |
| +0x20 | blocks: [MirBlock]  | 0x72886b1 (ptr, live) |
| +0x28 | entry_block: BlockId| 0x7288911 (ptr, live) |

So fields 1 and 3 are nil while 0/2/4/5 are live. `func.name == "main"`
therefore evaluates FALSE (observed `is_main` arg = 0x13, the nil/false
immediate), and `sig.return_type` is 0 -> SEGV.

The all-zero MirSignature is a *downstream* artifact: `build_signature`'s
prologue copies the struct into a fresh `rt_alloc(0x18)` and, when the source
fails the `tag==1 && ptr!=0` test, `cmove`s every field to 0. i.e. the
signature was already nil before the copy.

Tag encoding observed: `0x3` is the nil/false immediate; the truthiness test
compiled by stage2 is `cmp $0x13,%al; ja <true>; bt %eax,$0x80009; jb <false>`
(mask bits 0, 3, 19).

## Backtrace B — Lane Q's 16 "NOLOWER" SEGVs are a DIFFERENT crash site

`<stage2> compile src/compiler/30.types/simd.spl --format=smf`:
```
#0 0x5a3a1b hir_lowering._Items_.declaration_lowering.HirLowering.lower_function
#1 0x5adcf5 module_build.HirLowering.lower_module
#2 0x5abe33 module_build.HirLowering.lower_parser_module_unstub
#3 0xa9ae61 driver_hir_pipeline_lowering.CompilerDriver.lower_and_check_impl
#4 0xaa2ef8 driver_orchestration.CompilerDriver.compile
```
Faulting instruction (`lower_function+0x109b`):
```
5a3a0f: mov %rbx,%rdi
5a3a12: call rt_enum_payload
5a3a17: and $0xfffffffffffffff8,%rax
5a3a1b: mov (%rax),%rbx        # <-- rax == 0, SEGV. no nil guard
```
Preceded by `SymbolTable.get_symbol_type` + `rt_is_some` + the same
`cmp $0x13 / bt $0x80009` truthiness sequence.

**Conclusion for the coordinator: these are two DISTINCT crash sites in two
different compiler phases (backend vs HIR lowering) — not one bug by
backtrace.** They do share a defect *shape*: stage2's own generated code
performs an unguarded `and $~7; mov (%rax)` on a value that is nil at runtime,
where the same compiler emits a nil-guarded `cmove` sequence elsewhere. Whether
one systemic miscompile produces both is a hypothesis, not a finding.

## Prior art / scope

`.claude/rules/vcs.md` records (2026-08-18) that **all four** tracked
`bootstrap/**/simple` binaries already SEGV on both `compile` and
`native-build`, which predates goal-r4 — pointing at the producing codegen
(seed/stage1), not this bootstrap run.

## DECISIVE: the .spl source is correct; stage2 is MISCOMPILED

The identical compiler source, interpreted by the Rust seed, compiles the same
fixture end to end:

```
bin/simple run src/app/cli/bootstrap_main.spl compile build/lanes_s/h2.spl --format=smf -o build/lanes_s/h2i.smf
...
[cranelift-direct] module
[cranelift-direct] declare __simple_main      <- func.name resolved to "main"
[cranelift-direct] compile main
[cranelift-direct] emit /mnt/data/tmp/simple_cranelift_build.lanes_s.h2.o
```

Interpreted: `func.name == "main"`, signature populated, no crash.
Stage-2 native: `func.name == nil`, signature nil, SEGV at the same line.

**Therefore no edit to `cranelift_codegen_adapter.spl` or the MIR builder can
fix this.** The defect is a miscompilation introduced by the codegen that
PRODUCED stage2 (stage1 / the seed's native backend): reading a struct value
back out of a `Dict<SymbolId, MirFunction>` yields an object with a subset of
its fields nil'd. Fixing it means fixing the producing codegen's struct-valued
Dict read (or struct copy) path and redeploying, not patching the victim.

Corroborating: a `Dict<text, Outer>`-of-struct round-trip fixture
(`.values()` iteration, 6 fields incl. a nested struct) is CORRECT under the
seed interpreter — so the interpreter path is not implicated, only native
codegen.

## Open / UNKNOWN

- Whether the MirFunction fields are nil at dict-INSERT time or corrupted at
  dict-READ time (`rt_dict_values` copy). Not yet measured.
- Whether a freshly built native binary from current `main` reproduces the
  selective-nil-field pattern. The `E1002: function \`fun\` not found` that
  blocked this was a `fun` vs `fn` typo at `src/compiler/20.hir/hir_types.spl:212`
  in ANOTHER LANE'S UNCOMMITTED working-copy edit (origin/main is clean); fixed
  locally in the shared worktree so source-based compiles run again, NOT pushed
  as a source change.
- WHICH codegen construct is miscompiled — dict-value read, struct copy, or
  field-offset assignment. Not yet isolated to a minimal native fixture.
- Whether the same miscompile explains Lane Q/P's 152 HIR-phase SEGVs. Same
  defect shape, different site; unproven.
- No fix landed. Do not read this record as "diagnosed and repaired".

## CONFIRMED: minimal repro of the PRODUCER bug (2026-08-24)

`build/lanes_s/dv2.spl` — a 16-field struct (`Big`: nested struct, `text`,
arrays, `text?`, `i64?`, `Dict`) stored in a `Dict<i64, Big>` and read back via
`.values()`. Nothing compiler-specific; ~35 lines.

| run | output |
|-----|--------|
| seed interpreter (`bin/simple run`) | `name=[main] sig_ret=9 nlocals=0 nblocks=1 entry=3 sym=1` — CORRECT |
| seed `native-build` + execute | `name=[95505753971696] sig_ret=1 nlocals=1 nblocks=1 entry=95505753971696 sym=1` — **CORRUPT** |

Four of six probed fields are wrong in the native build:
- `name` (`text`) prints as a raw pointer value — the field holds a non-text word.
- `signature.return_type` reads 1, not 9.
- `locals.len()` reads 1, not 0.
- `entry_block` reads **the same garbage word as `name`** — i.e. two distinct
  fields alias the same slot. That is a field-offset / layout defect, not a
  lost write.
- `blocks.len()` and `symbol.id` happen to be right.

This is the same signature as the Stage-2 failure (`MirFunction` read out of
`Dict<SymbolId, MirFunction>` with `name` dead and other fields inconsistent),
reproduced in 35 lines with a build measured in minutes instead of a full
bootstrap. **The miscompiler is the Rust seed's native codegen
(`src/compiler_rust`), which is what produces Stage 2.**

Fixture: `build/lanes_s/dv2.spl` (and `dv4.spl`, which additionally probes
direct value, `d[k]` index read, `.values()` iteration and array element in one
program, to separate the dict from the struct layout itself).

### Still UNKNOWN at time of writing
- Whether the corruption needs the Dict at all (dv4 answers this).
- The exact codegen site. Not yet located in `src/compiler_rust`.
- No fix landed.

## LOCALIZED: only `for x in dict.values()` corrupts (2026-08-24)

`dv4.spl` probes four access paths against one `Dict<i64, Big>` in a single
native binary. Interpreted, all four are correct. Natively:

| path | result |
|------|--------|
| A direct value (`make()`) | CORRECT |
| B `d[1]` index read | CORRECT |
| C `for f in d.values()` | **CORRUPT** |
| D `a[0]` array element | CORRECT |

Disassembly of the built binary shows why. For the correct direct path,
`{direct.name}` compiles to `mov 0x8(%r15),%rdi` + `rt_interp_cstr` (offset 8,
text). Inside the `.values()` loop, `{f.name}` compiles to:

```
3315: mov (%r12),%rdi            # byte offset 0 — WRONG field
3319: call rt_raw_i64_to_string  # typed i64 — WRONG type
```

Every field read in the loop collapses to **byte offset 0 and i64 typing**,
which is why `name` and `entry_block` printed the identical word and
`symbol.id` printed the dict key.

The C runtime is NOT at fault: a direct C selfcheck of
`rt_dict_new`/`rt_dict_set`/`rt_dict_values`/`rt_for_iterable`/`rt_index_get`
against `build/simple-core/libsimple_runtime.a` round-trips the element pointer
exactly (`MATCH=1`). The defect is in compilation, not the runtime.

This matches the root cause already written down in-tree at
`src/compiler/70.backend/backend/interpreter.spl:145-175`: the seed erases
`Dict<K,V>` to `ANY` (`type_resolver.rs`: `"Dict" => TypeId::ANY`), so
`.values()` yields `ANY`-typed elements (`mod.rs`: `"keys"|"values" =>
TypeId::ANY`) and field access falls to the seed's "most-fields-wins" global
field resolver.

## DISPROVEN: the documented typed-binding workaround does NOT fix this

`interpreter.spl:145-175` and `.claude/rules/language.md` both prescribe binding
the element to a typed local (`val f: Big = f_`) as the remedy. Measured on a
native build (`dv6.spl`, identical to dv4 except for the binding):

```
expected:  name=[main] ret=9 nloc=0 nblk=1 entry=3 sym=1
dv4 (untyped): name=[<ptr>] ret=1 nloc=1 nblk=1 entry=<same ptr> sym=1
dv6 (typed):   name=[]      ret=0 nloc=0 nblk=0 entry=<ptr>      sym=1
```

The typed binding CHANGES the corruption (offset-0 collapse becomes a
mostly-zeroed decode) but does not repair it. **Do not apply the typed-binding
idiom as a fix for this and do not report it as one.** Five such edits were
made to `cranelift_codegen_adapter.spl` and `driver_aot_smf_output.spl` during
this investigation and were REVERTED once dv6 disproved them.

Notably the dv6 shape — mostly-zeroed fields with a few live — matches the
Stage-2 `MirFunction` observation better than dv4's does, suggesting two
stacked defects: untyped gives wrong field offsets, typed gives a wrong
element decode/copy.

### Where the fix goes — still UNDECIDED
Deciding evidence not yet gathered: whether the emitted MIR already carries
`byte_offset: 0` / an i64-typed element local. If it does, the fix is
Simple-side, in the elem-type stamping at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1446-1500`
(which already carries two prior bug comments about exactly this) plus
`lower_for_iterator` in `mir_lowering_stmts.spl`. If the MIR is correct, the
fix is in the Rust seed (`access.rs` most-fields-wins resolution /
`decode_runtime_value`). **No fix has landed.**

## REFUTED: it is not the "most-fields-wins" wrong-struct resolver either

`dv8.spl` is `dv4.spl` with every field name of `Big` and its nested structs
renamed to a globally unique `zzq_*` identifier, so no other struct in the
program (or the stdlib) declares any of them and the ambiguity heuristic in
`hir/lower/type_resolver.rs:get_field_info` has exactly one candidate.

```
expected:      name=[main]  ret=9 nloc=0 nblk=1 entry=3          sym=1
dv4 (colliding names): name=[<ptr>] ret=1 nloc=1 nblk=1 entry=<same ptr> sym=1
dv8 (unique names):    name=[<ptr>] ret=1 nloc=1 nblk=1 entry=<same ptr> sym=1
```

Byte-identical corruption. **The resolver is not picking the wrong struct — it
is not resolving at all, and the field read defaults to byte offset 0 with i64
typing.** The root-cause explanation recorded at
`src/compiler/70.backend/backend/interpreter.spl:145-175` ("most-fields-wins
picks the WRONG struct's field index") therefore does not explain this failure,
and neither does its typed-binding remedy (disproven above).

Two long-standing in-tree claims about this defect class are now empirically
disproven. Both should be corrected once the real mechanism is known; until
then, do not act on either.

### What the seed source says, and why it doesn't match observation
The seed already threads `HirType::Dict { key, value }`
(`hir/lower/type_resolver.rs`, "task #104"), `.values()` on a `Dict`-typed
receiver is already typed `Array { element: V }`
(`hir/lower/expr/mod.rs:1619`), and `get_iterable_element`
(`hir/type_registry.rs:188`) already unwraps `Array` to its element for the
for-loop binding. On paper the element should be typed `Big`. It is not.

Leading remaining hypothesis, NOT yet tested: the receiver `d` is not
`HirType::Dict` at all — `var d: Dict<i64, Big> = {}` may take its type from
the empty dict literal and drop the annotation, leaving `dict_kv == None` so
`.values()` falls to the `TypeId::ANY` arm. A `SIMPLE_TRACE_FIELD_GET=1` build
(the seed has this env-gated trace at `hir/lower/type_resolver.rs` and
`codegen/instr/fields.rs:78`) was launched to read out the actual resolution
decisions; result not yet in at time of writing.

Fixtures, all in `build/lanes_s/`: `dv2` (first repro), `dv4` (access-path
matrix), `dv6` (typed binding, disproves the remedy), `dv7` (alternative
iteration forms), `dv8` (unique field names, refutes the resolver story).

## A PROVEN WORKING REWRITE EXISTS (i64-keyed dicts)

`dv9.spl`, native build, same `Dict<i64, Big>`:

| form | native result |
|------|---------------|
| `for f in d.values()` (dv4 C) | CORRUPT |
| `for k in d.keys(): val g: Big = d[k]` (dv9 F) | **CORRECT** |
| copy into `[Big]` via `d[k]`, then iterate the array (dv9 H) | **CORRECT** |

So `for x in dict.values()` is the ONLY broken iteration form measured. Unlike
the typed-binding idiom, this rewrite is proven by execution, not by analogy.

`d.entries()` is not an option: it fails to build at all —
`MIR lowering error: unresolved method call: entries`.

**Caveat before applying it to the compiler:** the loops that crash Stage 2
iterate `Dict<SymbolId, MirFunction>` — a STRUCT-keyed dict — and
`backend/interpreter.spl:145-175` separately claims struct-keyed
`.has()`/`[]` lookups fail to find present entries. dv9 used i64 keys, so it
does not license the rewrite for the compiler's dicts. `dv11.spl` tests exactly
that (`Dict<Sym, Big>`, keys-reindex and values side by side); it is
interpreted-correct and its native result decides whether the rewrite is
usable where it is actually needed. Do not apply the rewrite to the adapter
until that result is in.

## Where the fix belongs: SIMPLE source, not the Rust seed

Settled by the diagnostic text itself. `native-build` fails dv7 with
`for-in over non-array iterables is not supported by native codegen yet
(#143)`, and that string lives in **`src/compiler/50.mir/mir_lowering_stmts.spl:2597`**
— Simple source, run as the native-build worker — not in `src/compiler_rust`.
The seed contributes Cranelift/LLVM codegen from the MIR the Simple lowering
produced.

The relevant Simple-side chain:
- `mir_lowering_stmts.spl:2540-2570` derives the loop `element_type` from the
  collection local's HIR type (`Array`/`Slice`) and then its MIR type
  (`Array`/`Slice`), defaulting to i64 otherwise. An i64 default is exactly the
  observed "offset 0, i64-typed" field read.
- `_MirLoweringExpr/method_calls_literals.spl:1446-1500` is the code that is
  supposed to stamp `Array(elem_type, 0)` onto the `rt_dict_values` result by
  recovering `Dict(k_type, v_type)` from `local_mir_type_of(receiver_local)`.
  It already carries two prior bug comments about this exact class
  (`native_dict_keys_iter_index`, `native_dict_call_result_keys_elem_type`).
  If that match does not yield `Dict(...)`, the element type stays i64.

Leading hypothesis for why the stamp misses, NOT yet confirmed: `var d:
Dict<i64, Big> = {}` takes its MIR type from the EMPTY dict literal (no values
to infer V from) rather than from the annotation, so `local_mir_type_of` has no
usable `V`. `dv10.spl` (identical but `= {1: make()}`) tests this; result
pending.

For reference the Rust seed side already looks correct and is probably not the
fix site: `type_resolver.rs` threads `HirType::Dict{key,value}`,
`hir/lower/expr/mod.rs:1619` types `.values()` as `Array{element: V}`, and
`type_registry.rs:188 get_iterable_element` unwraps `Array`.

## dv10 / dv11 results, and why the per-site rewrite was NOT landed

`dv10` (`var d: Dict<i64, Big> = {1: make()}`, a NON-empty literal so V is
inferable): still CORRUPT, byte-identical to dv4. **The "empty dict literal
drops V" hypothesis is refuted.**

`dv11` (`Dict<Sym, Big>`, a STRUCT-keyed dict):
```
K_len 1
K_structkey_reindex  name=[main]  ret=9 nloc=0 nblk=1 entry=3 sym=1   CORRECT
L_structkey_values   name=[<ptr>] ret=1 nloc=1 nblk=1 entry=<ptr> sym=1  CORRUPT
```
So the keys-reindex rewrite works for struct-keyed dicts too — and this is a
**third disproven in-tree claim**: `backend/interpreter.spl:145-175` says
struct-keyed `.has()`/`[]` lookups fail to find a present entry. Measured here,
`d.len()` is 1 and `d[k]` returns the correct struct. Do not route around
`d[k]` on that basis.

### Census: the per-site rewrite is not a path to a working Stage 2
```
for x in <...>.values():   89 sites under src/compiler/,  91 src-wide
```
Every one of them is miscompiled when the seed builds Stage 2. Rewriting the
adapter's five would only move the SEGV to the next site — plausibly Lane Q's
`HirLowering.lower_function`. The rewrite was implemented, measured to be
correct at fixture level, and then **deliberately reverted**: it is a bridge,
not a fix, and landing it would have created a false impression that Stage 2
was unblocked. It is documented here so it can be reapplied deliberately if
someone needs to get past the adapter to expose the next crash site.

Not covered by that rewrite in any case: `driver_aot_smf_output.spl:169`
(`for fn_ in module.functions.values(): if fn_.has_driver_manifest_attr`) is in
the same Stage-2 path and equally miscompiled.

### Current state of the root-cause hunt
The element-type chain is Simple-side and runs INTERPRETED inside the
native-build worker, so it has a minutes-long iteration loop with no bootstrap
rebuild. A level-gated probe (`SIMPLE_TRACE_DICT_ELEM=1`, default off) was added
to `_MirLoweringExpr/method_calls_literals.spl` to read out whether the
`case Dict(k_type, v_type)` match actually fires for the `.values()` receiver
and what element type gets stamped. Result not yet in.

Remaining suspects, in order:
1. the `local_is_runtime_dict(dict_recv_local)` gate (:1440) never sets
   `receiver_is_dict`, so the whole typed-stamp block is skipped;
2. the stamp fires but `lower_for_iterator` reads the raw call result rather
   than the stamped temp;
3. `local_mir_type_of(receiver_local)` returns something other than `Dict(k,v)`.

Refuted so far: most-fields-wins wrong-struct resolution (dv8), typed-binding
remedy (dv6), empty-literal V loss (dv10), struct-keyed lookup failure (dv11),
C runtime (direct selfcheck).

## ROOT CAUSE LOCATED (2026-08-24)

The `SIMPLE_TRACE_DICT_ELEM=1` probe run on `dv4.spl` prints:

```
[dict-elem-probe] method=values recv_local=52
    recv_mir_type=MirTypeKind::Dict((MirType(kind: MirTypeKind::I64),
                                     MirType(kind: MirTypeKind::Struct(SymbolId(id: 1000000002)))))
[dict-elem-probe] stamped elem_type=MirTypeKind::Struct(SymbolId(id: 1000000002)) for method=values
```

So the **MIR side is entirely correct**: the receiver really is
`Dict(i64, Struct(Big))`, the `case Dict(k_type, v_type)` match fires, and the
`.values()` result is stamped `Array(Struct(Big), 0)`. Suspects 1 and 3 from the
list above are refuted, as is any story about the MIR element type.

The gap is one layer up. Field-access *indices* are resolved from the HIR type
of the receiver, not from the MIR type — and the Simple HIR/type layers have no
knowledge of dict method return types at all:

```
grep -rn '"values"\|"keys"' src/compiler/20.hir/ src/compiler/30.types/ src/compiler/35.semantics/
  -> no matches
```

Every `"values"`/`"keys"` occurrence in the compiler is in `10.frontend`
(interpreter), `15.blocks`, `50.mir` or `70.backend`. Nothing types
`Dict<K,V>.values()` as `[V]` in HIR. Consequently the for-loop variable's HIR
type is unresolved, `f.name` gets no field index, and lowering emits byte
offset 0 with i64 typing — exactly what the disassembly shows.

**Fix direction:** teach the Simple HIR/type layer the dict method return types
(`values -> [V]`, `keys -> [K]`, and the neighbours `get`/`remove` -> `V`),
mirroring what the Rust seed already does at
`compiler/src/hir/lower/expr/mod.rs:1619`, so the for-loop variable carries the
real struct type and field indices resolve. That is one fix for all 89 sites.

This has NOT been implemented. It is a change in the type layer and needs its
own design + verification pass; do not assume it is done.

### Reproduce pair for whoever lands the fix
- `build/lanes_s/dv4.spl` — fails before (C_values corrupt), must pass after.
- `build/lanes_s/dv11.spl` — struct-keyed neighbour, same requirement.
Both are interpreted-correct today, so the assertion is simply
"native output == interpreted output".

## NOT REPRODUCIBLE on aarch64-apple-darwin, at HEAD *or* at Lane S's own tree (2026-08-24)

This answers the standing question in Open/UNKNOWN above — "whether a freshly
built native binary from current `main` reproduces the selective-nil-field
pattern". On this host, at two different trees, with both backends: **no.**

Measured on macOS 25.5.0 / arm64, worker = a seed built fresh from the tree
under test (`cargo build --release --bin simple`, 1m53s). The Jul-25 deployed
seed on this mac is unusable for the question — it cannot parse current stdlib
(`unsafe(capabilities: [ffi]):` blocks, `signal_stubs.spl`) nor current
compiler source — so every run below uses the fresh seed.

| fixture | tree | native result |
|---------|------|---------------|
| dv4 shape, 6-field `Big` | `6eb889a1b07` (HEAD) | **CORRECT** (A/B/C/D all match interpreted) |
| dv4 shape, 6-field `Big`, `--backend=cranelift` | HEAD | **CORRECT** |
| dv4 shape, **16-field** `Big` (nested struct, `text?`, `i64?`, arrays, `Dict` field — the doc's dv2/dv4 shape) | HEAD | **CORRECT** |
| dv11 shape, `Dict<Sym, Big>` struct-keyed | HEAD | **CORRECT** (both K and L rows) |
| dvF — dict as a STRUCT FIELD, populated in one function, iterated via a param in another (the actual Stage-2 `module.functions.values()` shape) | HEAD | **CORRECT** |
| 16-field dv4 shape | `0299186137d` (Lane S's own probe commit) | **CORRECT** |
| dv4 shape, `--entry-closure` | HEAD | **CORRECT** |

`SIMPLE_MIR_FIELD_TRACE=1` explains why, and is the load-bearing measurement
here: `field-idx-fallback0` fires **0 times** in every one of those builds.
`resolve_field_index` never reaches its `0  # Default fallback` on this host,
so the "offset 0, i64-typed" collapse that the disassembly section above
documents simply does not occur — the loop variable's HIR type annotation
resolves and the second tier of the chain answers.

`SIMPLE_TRACE_DICT_ELEM=1` reproduces Lane S's probe output verbatim on this
host (`recv_mir_type=Dict(I64, Struct(SymbolId(id: 1000000002)))`, `stamped
elem_type=Struct(...)`), confirming the MIR half is correct here too.

**Conclusion: the miscompile is specific to the x86_64-unknown-linux-gnu lane
and/or to the binary that produced Lane S's stage2 — it is not a property of
the Simple source at `main`.** A mac lane cannot serve as the oracle, so no
fix was landed from here. The reproduce pair remains valid for the Linux lane.

One extra datapoint from the same sweep: `SIMPLE_BOOTSTRAP=1` *plus*
`--entry-closure` makes the 6-field dv4 fixture SEGV immediately on this host
(`Fatal: SIGSEGV ... __simple_main + 136`, before any output). `field-idx-fallback0`
is still 0 for that build, so it is a different defect, not this one. Not chased.

### Refinement of the fix direction — a FOURTH mechanism, not the three suspects

The three suspects were already settled by Lane S's probe (1 and 3 refuted
outright; 2 refuted in its literal form — `lower_for_iterator` *does* read the
stamped `Array(...)` type, which is where `element_type = Struct(Big)` comes
from). The real gap, from reading the chain end to end, is **neither HIR typing
nor the MIR element type**:

`resolve_field_index` (`50.mir/_MirLowering/function_lowering.spl:1243`) states
its own rule in its leading comment — *"Numeric SymbolIds are local to each
module and can collide in an entry-closure build. A lowered local's name-keyed
provenance is therefore authoritative when available."* Its FIRST tier is
`struct_value_syms[base_local]`, a NAME, not a type. That entry is written for
a for-loop variable by exactly one place — `lower_for_array_indexed`
(`mir_lowering_stmts.spl`, `if for_has_real_struct_name: self.struct_value_syms[loop_var.id] = fesn`)
— and only when `array_element_struct_syms` holds a real name **for the
collection local**. Nothing ever writes that map for a `rt_dict_values` /
`rt_dict_keys` result: the stamp at
`_MirLoweringExpr/method_calls_literals.spl:1520-1530` sets the MIR type and
`runtime_array_locals`, and stops there.

That is precisely the gap bug **#189** already closed for the `d[k]` index-read
path in `expr_dispatch.spl:1143-1195` (two tiers: the result type's own
`Struct(symbol)` name, then the store-side name recorded by
`note_container_elem_type`) — which is why dv4's path B is CORRECT and path C
is not. So the minimal fix is to mirror #189's two tiers onto the
`.values()`/`.keys()` result local, not to teach the HIR/type layer dict method
return types; the "teach HIR" paragraph above should be read as superseded by
this, pending verification.

**Two cautions for whoever implements it**, both measured here:
- Tier one cannot be `symbols.get_symbol_raw(sym.id).name` alone. The id in
  `Struct(SymbolId(id: 1000000002))` is a SYNTHETIC canonical id minted from
  base `1000000000` by `canonical_mir_type_symbol`
  (`_MirLowering/module_lowering.spl:344-356`); it is not an HIR symbol and
  `get_symbol_raw` returns nil for it. A reverse map (`canonical id -> bare
  name`, written at both mint sites — `module_lowering.spl:353` has `info.name`
  in scope, `switch_operators_calls.spl:639` derives it from `shape`) is needed
  for that tier to do anything.
- The store-side tier (`array_element_struct_syms.get(receiver_local.id)`) is
  per-function state, so it cannot cover the Stage-2 shape at all
  (`module.functions` populated in one function, iterated in another). It must
  also be restricted to `values`: that map records the VALUE struct name, and
  applying it to `.keys()` on a struct-KEYED dict would stamp the wrong struct.

**This analysis is UNVERIFIED.** It is code-reading plus the B-correct /
C-corrupt asymmetry, not execution: no fixture on this host exercises the
fallback, so nothing here was proven by running it. Do not land it as a fix
without a corrupt→correct measurement on the Linux lane.

### Harness gaps that block a macOS lane (both hit here)
- `setsid` does not exist on macOS and the native-build worker spawns through
  it — `exec: setsid: not found`, worker exit 127. Shim required.
- The hosted entry stub declared `__simple_startup_before_main` with
  `__attribute__((weak))`, which on Mach-O is not a weak-UNDEFINED symbol, so
  **every** hosted `native-build` on macOS failed to link. Fixed in the same
  change as this note (`llvm_native_link_hosted_support.spl`, weak DEFINITION
  under `#if defined(__APPLE__)`, mirroring the seed's own `_main_stub`).
  `weak_import` was tried first and does NOT work when the symbol exists in no
  input at all.

## 2026-08-24 (later) — the HIR fix direction is now IMPLEMENTED, and the host's oracle situation is not what it looked like

### The "NOT implemented" fix direction landed at `c9da626ec1c`

This record's fix direction — *type `Dict<K,V>.values()` as `[V]` (and `keys()`
likewise) in the Simple HIR layer, mirroring the Rust seed's
`hir/lower/expr/mod.rs:1619`* — is implemented. Located site, so nobody has to
find it again:

- **File:** `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`,
  function `me lower_hir_expr(e: Expr) -> HirExpr`.
- **Two insertion points, both patched:** the discriminant-gated MethodCall
  pre-dispatch arm (terminal return, was `:175-179`) and the big-match MethodCall
  fallback arm (was `:557`). Patching one only would make typing depend on which
  duplicated arm fires, and a *defeated* kind pre-dispatch is exactly what
  `bootstrap_stage2_empty_mir_bodies_2026-07-05.md` localises for statements.
- **Precedent to copy from:** the `ExprKind.Index` arm at `:474-489` in the same
  function already does this for `d[k]` (`case HirTypeKind.Dict(_, value)`).
  Its caveat is load-bearing: `has_type_` is the AUTHORITATIVE presence bit;
  `type_ != nil` alone lets a zeroed placeholder be interpreted and SIGSEGVs
  later in `lower_hir_block`'s 16-byte HirType clone.
- **Type shapes:** `HirTypeKind.Array(element: HirType, size: i64?)` and
  `HirTypeKind.Dict(key: HirType, value: HirType)`, `20.hir/hir_types.spl:516-519`.
  There is **no TypeId and no interning API** in the pure-Simple layer
  (`grep TypeId 20.hir/hir_types.spl` -> zero matches); `HirType` is a plain
  structural value built inline.

Why not the two later passes, so they are not re-investigated:

- `35.semantics/resolve.spl:483` is the only place that assigns a method-call
  result type today, but it goes through `resolve_call_result_type_raw`
  (`resolve_lookup_helpers.spl:73-88`), which needs a **resolved user symbol**.
  A builtin `Dict.keys()` has none, so it returns the `nil` fallback. It also
  writes back `has_type_: expr.has_type_` at `:754`, so a type set there without
  flipping that bit would be invisible downstream.
- `30.types/type_infer/inference_expr_calls.spl:54-93` (`infer_method_call`) has
  the receiver type in hand but ends in an unconstrained `fresh_var`, and
  **nothing in `30.types/type_infer/` writes back into the HIR** (`grep '\.type_ ='`
  -> zero matches). Its driver is Advisory by default and runs AFTER resolve.

Grep evidence that no per-method result-type table existed anywhere in the
pure-Simple layer before this: `"keys"`/`"values"` across `20.hir`, `30.types`,
`35.semantics`, `25.traits` -> **zero matches**;
`30.types/type_system/builtin_registry.spl:121` registers name/arity/doc with no
return type; `30.types/type_infer/traits.spl:214`'s `case "to_string":` is a
trait-obligation stub whose arms are literally `pass`.

**Still unverified, and it must be said plainly:** the typing was not exercised.
Nothing was compiled or run through the pure-Simple pipeline, so no dict loop
variable was observed acquiring its element type and the arm64 32-bit mask was
not observed disappearing. The change is a mechanical mirror of the seed's arms
plus this file's own Index-arm idiom, +74/-0, entirely behind a
`keys`/`values` + zero-args + `has_type_` + `HirTypeKind.Dict` gate.

### Oracle situation on aarch64-apple-darwin (measured 2026-08-24)

Correcting an assumption that cost time in more than one lane here:

- **The deployed self-hosted binary is dead for compiling.**
  `bin/release/aarch64-apple-darwin-macho/simple` (132,398,344 bytes, 2026-08-10;
  `bin/simple` is a 431-byte exec wrapper pointing at it) cannot `native-build` a
  three-line hello world: `error: in-process native-build: AOT compile error in
  h: <invalid-heap:0xafd011821>`. It also has no `lint` (bootstrap CLI: only
  `compile` and `native-build`).
- **`simple_seed` DOES work and is a usable oracle.**
  `bin/release/aarch64-apple-darwin-macho/simple_seed` (20,392,352 bytes,
  2026-07-25) runs Simple source correctly (`run h.spl` -> `hello`, rc=0) and
  parses `.spl` files, so `simple_seed run <file>` is a genuine PARSE check for
  an edited compiler source (a parse failure is reported as
  `error: compile failed: parse: in "<file>": ...`). This is how `c9da626ec1c`
  was parse-verified. Note it exercises the seed's own Rust frontend, so it does
  NOT exercise pure-Simple HIR/MIR changes.
- **`simple_seed lint` is unusable** — it dies before reaching any target file:
  `parse: in ".../src/compiler/35.semantics/lint/raw_sffi_call.spl": Unexpected
  token: expected expression, found Dedent`. Pre-existing; last touched by
  `b77e6effd9e`. Filed here rather than separately because it is the reason the
  parse check above had to be done the long way.
- **Anyone measuring a compiler source edit must pass `--fresh-cache`**: a warm
  rebuild after a real edit produced a BYTE-IDENTICAL binary
  (`3 compiled, 747 cached`) — see
  `stage3_native_build_and_monomorphize_segv_at_origin_main_arm64_2026-08-24.md`.
  A "nothing changed" reading from a warm build proves nothing.

## 2026-08-24 (later still) — CORRECTION: the interpreted lane WORKS, and binary diffing does not

Two corrections to the section above, both of which change how a compiler
change gets verified on this host. The first is an unlock; the second is a trap.

### 1. A freshly built seed runs the pure-Simple compiler end to end

The section above said the deployed binary cannot compile and that
`simple_seed lint` dies in `35.semantics/lint/raw_sffi_call.spl`. Both are true
of the **deployed 2026-07-25 seed**. They are NOT true of a seed built from
current source:

```
cd src/compiler_rust && cargo build --release --bin simple      # 2m08s
target/release/simple run src/app/cli/bootstrap_main.spl native-build hello.spl
```

That **compiles, links, and the produced binary RUNS**. So this host has a
working compile-and-run oracle for pure-Simple compiler changes, without any
Stage-2 rebuild and without the 845s `--fresh-cache` cost. A dict fixture
native-built this way executes and prints the right answer.

The stale seed's blocker was one grammar form, not a broken tree: a multi-line
boolean condition whose continuation line is indented to the BODY's level, e.g.

```
        if (part.starts_with("rt_") or part.starts_with("spl_")) and
            not externs.contains(part):
            externs.push(part)
```

The old seed reports `parse: Unexpected token: expected expression, found
Dedent`; the current seed parses it. **Do not "fix" this by reformatting the
sources** — a census counts **1,114 occurrences across `src/`** (top files:
`80.driver/driver_vhdl_artifacts.spl` 41, `os/hosted/hosted_browser_renderer_process.spl`
35, `gc_async_mut/gpu/engine2d/draw_ir_adv.spl` 26). It is an idiomatic form;
rewriting it would be exactly the silent normalization CLAUDE.md forbids. Build
a current seed instead.

Verified end to end this way: `c9da626ec1c` was proven INERT and its replacement
`fb7e76c489a` proven to fire, by instrumenting the gate and reading probe output
out of the running compiler.

### 2. Binary diffing is NOT a valid oracle here — do not use `cmp`

**The build is not byte-reproducible.** Control experiment: same directory, same
cold cache, pristine source vs patched source, and separately two builds whose
source difference cannot possibly matter:

| fixture | control | treatment | bytes | size |
|---|---|---|---|---|
| dict loop | pristine | patched | DIFFER | 71624 = 71624 |
| **hello world** (no dict at all) | pristine | patched | **DIFFER** | 35224 = 35224 |

Hello world contains no dict and is unaffected by the change under test, yet its
bytes differ between builds. Size is stable; content is not. Build path also
perturbs size: the identical tree built at `/tmp/wt_base` and `/tmp/wt_fix`
produced 71616 vs 71624.

So "the binary changed, therefore my fix did something" is unsound here, and so
is the converse. Use instrumented probe output and program EXECUTION. This also
means a byte-identical result is not automatically the warm-cache trap — check
`hir-cache hits=` before concluding either way.

### 3. `ands #0xfffffff8` does not reproduce at fixture scale

Every build measured here — patched and unpatched — has **mask32 = 0**. The
32-bit-mask defect shows up when Stage 2 compiles the compiler itself, not on a
small dict fixture. Zero masks on a fixture is NOT evidence that a fix removed
them, and must not be reported as such.
