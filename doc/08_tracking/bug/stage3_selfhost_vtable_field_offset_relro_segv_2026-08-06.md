# Stage 3 self-host SIGSEGV: a cross-module field read on a vtable-bearing class uses the WRONG offset and writes into read-only RELRO

- **Date:** 2026-08-06
- **Severity:** critical — this is the current Stage 3 self-host blocker (#5),
  reached only after blockers #1-#4 are in place.
- **Status:** root-caused to machine-code level with a gdb backtrace + objdump
  + ELF section evidence. **NOT fixed** — the defective code generator is the
  **Rust seed**, not any `.spl` file (see "Fix layer / scope decision").
- **Not** the same defect as
  `mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`
  (that one is a `call 0` from an unresolved builtin in the CodegenError
  *reporter*). **New and unrelated.**

## Failure mode, with the measurement that establishes it

Real **SIGSEGV, exit 139, core dumped** (`timeout: the monitored command
dumped core` / `Segmentation fault`) at ~394 s.

- **Not a stack overflow.** `VmStk: 132 kB`, flat across the whole run
  (sampler output `build/cyc/FIX1RUN/mem.log`). This is the same single
  measurement that separated blockers #2 and #3.
- **Not an external kill.** gdb stopped on the signal and produced a
  backtrace; earlyoom would be exit 137/143 with no core.
- **Not an OOM.** Peak RSS 10.7 GB, far below the 55-81 GB earlyoom band.
- **Not a fatal-MIR-error reporter crash** (the coordinator's open question).
  MIR lowering had *completed*; zero MIR errors were pending. No diagnostic was
  emitted because nothing had failed yet.
- **Not in MIR lowering at all.** The `[mir-lower-expr]` traces that ended the
  log are stdout (block-buffered) and merely the last flushed block; the
  authoritative stderr stream and the gdb backtrace both put the fault in the
  LLVM backend.

## Backtrace (gdb, launched under gdb — `ptrace_scope=1` blocks attach)

```
Program received signal SIGSEGV, Segmentation fault.
rip 0x63ce58  <LlvmIRBuilder.emit_module_header+952>
rax 0x0   rbx 0x6591a60

#0  LlvmIRBuilder.emit_module_header ()
#1  compiler.driver.driver_bootstrap.bootstrap_emit_real_llvm_object ()
#2  compiler.driver.driver_bootstrap.compile_bootstrap_context_to_native ()
#3  app.cli.bootstrap_main.run_native_build_bootstrap ()
#4  main ()

=> 0x63ce58: movq $0xb,0x38(%r13)      # self.header_emitted = true
   0x63ce60: mov  0x40(%r13),%rdi      # self.pending_baremetal_attrs
```

`0xb` = 11 = `SPECIAL | (1 << 3)` = the runtime encoding of `true`, which pins
the faulting instruction to `self.header_emitted = true` at
`src/compiler/70.backend/backend/llvm_ir_builder.spl:141`. Corroborated by the
missing `[bootstrap-real-llvm] count` print (`driver_bootstrap.spl:333`, the
line right after `emit_module_header()` at :330) — it never appears in the log.

## Root cause (proven, not inferred)

`self` (`rbx`) at the fault is **`0x6591a60`**, which `nm` resolves to:

```
0000000006591a60 D __vtable__compiler__backend__backend___MirToLlvm__class_def__MirToLlvm__for__MirTextCodegen
```

— a **vtable**, inside `PT_GNU_RELRO` (`0x65902f0 + 0x513d10`, section
`.data.rel.ro`), which the loader `mprotect`s **read-only** after relocation.
So field *reads* at `0x0(%r13)` earlier in the same function succeeded, and the
first field *write* faulted: `SEGV_ACCERR`, a write to read-only memory. This
is the rare SIGSEGV shape where the pointer is perfectly mapped.

A second, independently instrumented gdb run (`GDBRUN2`) reproduces this
**2/2** and closes the loop exactly:

```
$1 = 0x6591a60                            # $r13
$2 = (void *) 0x6591a98 <__vtable__...MirToLlvm__for__MirTextCodegen+56>   # si_addr
$3 = 2                                    # si_code == SEGV_ACCERR (write to read-only)
0x6590000  0x6aa4000  r--p  .../FIX1/stage2-simple      # the RELRO mapping, read-only
```

`si_addr` is literally `<vtable>+56` = `+0x38`, the `header_emitted` slot, and
`si_code = 2` (`SEGV_ACCERR`) rules out an unmapped-address fault: the memory is
mapped, it is simply not writable.

`self` is a vtable because the caller read the wrong field offset:

| site | file | instruction | offset used |
|---|---|---|---|
| constructor `MirToLlvm.create` | `70.backend/backend/_MirToLlvm/class_def.spl:169` | `0x5e81c0: mov $0x6591a60,%rcx; mov %rcx,(%rax)` then `mov %rcx,0x8(%rax)` for `builder` | vtable at **0**, `builder` at **+8** |
| in-class read `self.builder` | `70.backend/backend/_MirToLlvm/core_codegen.spl:180` | `0x5e9146: mov 0x8(%r14),%rdi` | **+8** — correct |
| cross-module read `translator.builder` | `80.driver/driver_bootstrap.spl:329,330` | `0x705d8e / 0x705d99: mov (%rbx),%rdi` | **0** — WRONG, reads the vtable slot |

`MirToLlvm` declares `builder` as its **first** field
(`class_def.spl:27`) and has `impl MirTextCodegen for MirToLlvm`
(`core_codegen.spl:163`), so it carries a vtable header word at offset 0 and
every field is shifted by 8. `driver_bootstrap.spl` does not apply that shift.

### Where the wrong decision is made

Rust seed, `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs`
(the whole-project "native object layout" pass), for `MirInst::FieldGet` /
`FieldSet`:

- `resolve_exact_owner(name)` resolves a bare owner name through
  `local_globals` -> `use_map` -> `import_map` (:1587-1595).
- When it resolves, `owner_has_vtable = Some(vtable_type_owners.contains(&owner))`
  (:1664) — correct.
- When it does **not** resolve and the name is not in `ambiguous_names`, the
  final `else` sets **`owner_has_vtable = Some(false)`** (:1689) with the
  comment "the project-wide scan is exhaustive ... an unresolved builtin/generic
  owner therefore has no native object header".
- The `owner_name: None` arm likewise forces `Some(false)` (:1707).

Both of those are **fail-open**: an owner the pass could not resolve is
silently declared header-less, and every field access through it is
off-by-one-slot. `driver_bootstrap.spl` imports `MirToLlvm` through a
**re-export facade** (`use compiler.backend.llvm_backend.{MirToLlvm, ...}`,
:12) while the class is actually defined in
`compiler.backend.backend._MirToLlvm.class_def` — so the owner key the pass
derives there does not match the one `vtable_impls`/`StructInit` derived in the
defining module, and the fallback picks "no vtable".

This is structurally the SAME shape as blocker #4 (`unresolved type: ByteOrder`):
**the generated code depends on HOW a name was imported, not on what the code
does with it.**

### Blast radius (larger than the one crash)

Every `translator.<field>` access in `driver_bootstrap.spl` is shifted by one
slot, not just `.builder`: `translator.unknown_func_decls`,
`translator.defined_func_names`, `translator.builder.build()`, and the reads in
`bootstrap_emit_llvm_trailer`. Only `.builder` (field index 0) crashes, because
only it lands on the RELRO vtable pointer; the rest read a neighbouring field's
value **silently**. A fix that only rewrites the crashing call site would
convert a loud SIGSEGV into a silently wrong LLVM module.

## Fix layer / scope decision (why this is NOT fixed here)

The crashing binary is **stage2**, whose machine code was produced by the
**Rust seed** (`build_stage2.sh` runs the seed with
`SIMPLE_NATIVE_BUILD_RUST=1`). No `.spl` edit can change stage2's behaviour on
this cycle. The correct-layer fix is therefore in the Rust seed's native-project
layout pass, at the two fail-open branches above — most likely: consult the
`all_mangled` bare-name suffix index (the logic the `ambiguous_names` branch
already implements at :1668-1681) *before* defaulting to `false`, and make a
genuinely unresolvable class-typed owner **fail closed** (an `Err`) instead of
guessing a layout.

Two options were considered and **rejected**:

- *"Add the missing import to `driver_bootstrap.spl` so the layout agrees."*
  Rejected: layout depending on imports is the bug; exploiting it is a
  cover-up that silently un-fixes itself on any import reorder.
- *"Wrap the access in a method on `MirToLlvm`."* Rejected: it fixes only
  `.builder` and leaves the other shifted accesses reading wrong fields
  silently.

Handing the seed change back for scoping rather than implementing it silently:
it touches cross-module owner resolution in the seed, requires a seed rebuild
(which would replace the pinned `stage2-runtime-authority` seed), and the
"fix `.spl` not Rust" rule cannot apply to a defect in the seed's own code
generator.

**Second, separate finding to check:** the pure-Simple compiler's own
field-offset lowering (`src/compiler/50.mir`, `src/compiler/70.backend`) mirrors
this seed logic and very likely carries the same visibility-dependent fallback.
That does not cause the present crash (stage2 is seed-built) but would
reproduce it from stage3 onward. Not audited here.

## Reproduction

```
sh /home/ormastes/dev/simple-s3bisect/build/cyc/gdb_stage3.sh FIX1 GDBRUN1 1800
```

`FIX1/stage2-simple` is a stage2 built from a tree carrying blockers #2, #3 and
#4's fixes. Evidence retained under
`/home/ormastes/dev/simple-s3bisect/build/cyc/{FIX1RUN,GDBRUN1}`.
