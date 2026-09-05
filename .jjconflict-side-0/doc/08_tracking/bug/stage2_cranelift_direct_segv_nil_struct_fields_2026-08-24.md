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

## Open / UNKNOWN

- Whether the MirFunction fields are nil at dict-INSERT time or corrupted at
  dict-READ time (`rt_dict_values` copy). Not yet measured.
- Whether a freshly built native binary from current `main` reproduces the
  selective-nil-field pattern (minimal fixture written, native-build blocked
  by an unrelated `error[E1002]: function \`fun\` not found` sweeping a stray
  file into the build).
- No fix landed. Do not read this record as "diagnosed and repaired".
