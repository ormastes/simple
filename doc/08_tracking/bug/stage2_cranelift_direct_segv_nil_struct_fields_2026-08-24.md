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
