# Stage 3 self-host SIGSEGV: a cross-module field read on a vtable-bearing class uses the WRONG offset and writes into read-only RELRO

- **Date:** 2026-08-06
- **Severity:** critical — this is the current Stage 3 self-host blocker (#5),
  reached only after blockers #1-#4 are in place.
- **Status:** root-caused to machine-code level (gdb + objdump + ELF), FIXED in `.spl` as a two-line workaround; the underlying Rust-seed fail-open remains open. RED/GREEN + sabotage below.
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

Both of those are **fail-open**: an owner the pass cannot name is silently
declared header-less, and every field access through it is off-by-one-slot.

**Which branch fires was measured, not guessed.** In the *same source file*,
`bootstrap_emit_llvm_trailer` reads `translator.unknown_func_decls` (field
index 19) at `0xa0(%rbx)` = `19*8 + 8` and `translator.defined_func_names`
(index 20) at `0xa8(%rbx)` = `20*8 + 8` — both **vtable-aware and correct**.
Same file, same imports, same class. So the import path is NOT the
discriminator, and the "re-export facade" hypothesis is refuted.

The actual discriminator is **how the receiver local got its type**:

| receiver | binding | `owner_name` at MIR lowering | offset |
|---|---|---|---|
| `bootstrap_emit_llvm_trailer(translator: MirToLlvm)` | typed **parameter** | `Some("MirToLlvm")` -> resolves | `+8` correct |
| `bootstrap_emit_real_llvm_object`: `var translator = MirToLlvm.create(...)` | local **inferred from a `static fn` return** | `None` -> forced `Some(false)` | `0` WRONG |

`lowering_expr_struct.rs:275` derives `owner_name` from
`type_registry.get_type_name(receiver_ty)`. A local whose type came from a
static-constructor return carries no named type there, so `owner_name` is
`None`, and the `owner_name: None` arm at :1707 forces `owner_has_vtable =
Some(false)` — guessing "no header" for a class that has one.

This is structurally the SAME shape as blocker #4 (`unresolved type: ByteOrder`):
**the generated code depends on HOW a name was bound, not on what the code does
with it.**

### Blast radius

Measured, not inferred: only the accesses in `bootstrap_emit_real_llvm_object`
and `bootstrap_emit_real_llvm_module_object` (the two functions binding
`translator` from `MirToLlvm.create(...)`) are shifted. The typed-parameter
reads in `bootstrap_emit_llvm_trailer` are correct. Of the shifted ones, only
field index 0 (`.builder`) crashes, because only it lands on the RELRO vtable
pointer; the others would read a neighbouring field **silently**.

## Fix applied

`src/compiler/80.driver/driver_bootstrap.spl:328,369` — give the local the
explicit type its sibling function's parameter already has:

```
var translator: MirToLlvm = MirToLlvm.create("app.cli.bootstrap_main", CodegenTarget.Host, nil)
```

This is not an import-order trick: it makes the receiver's named type available
to `type_registry.get_type_name`, which is precisely the input the layout pass
needs and the same input a typed parameter already supplies. Two lines, no
behavioural change other than the layout decision.

**It is a workaround for a real Rust-seed defect, not the root fix.** stage2's
machine code is produced by the seed (`build_stage2.sh` runs the seed with
`SIMPLE_NATIVE_BUILD_RUST=1`), so the fail-open at
`native_project/compiler.rs:1707` is still live and will mis-lower any *other*
field access on a vtable-bearing class through an un-named local. The correct
root fix is in that pass: an unresolvable **class-typed** owner must fail
closed (an `Err`) rather than being guessed as header-less, and/or
`owner_has_vtable` should be resolved from the receiver's MIR type rather than
from a name that inference may not have. Not done here: it requires a seed
rebuild, which would replace the pinned `stage2-runtime-authority` seed that
every lane measures against.

**Second, separate finding, not audited here:** the pure-Simple compiler's own
field-offset lowering (`src/compiler/50.mir`, `src/compiler/70.backend`) mirrors
this seed logic and may carry the same fallback. It cannot cause the present
crash (stage2 is seed-built) but would reproduce it from stage3 onward.

## RED / GREEN (FIX1 and FIX2 differ ONLY by these two lines)

| | stage2 | machine code at the `.builder` read | Stage 3 result |
|---|---|---|---|
| RED | `FIX1` | `0x705d8e: mov (%rbx),%rdi` | **exit 139**, SIGSEGV, core dumped, 394 s — reproduced **2/2** (`FIX1RUN`, `GDBRUN1`, `GDBRUN2`) |
| GREEN | `FIX2` | `0x705d9e: mov 0x8(%rbx),%rdi` | **exit 1**, no signal, 393 s |

`FIX1` is the identical tree with the annotation absent, so it doubles as the
sabotage pass: removing the two annotations restores the exact SIGSEGV at the
exact address.

Stage 3 now runs well past this wall: it emits the module header, translates
**5,674** bootstrap MIR functions and **86** statics, and writes a 5.9 MB
`.ll`.

## Next blocker (#6) — distinct, characterised separately

`llc` rejects the emitted IR:

```
llc: error: unable to get target for 'unknown-linux-<enum@0x27c1498b0>'
```

The `target triple` line built in `emit_module_header`
(`llvm_ir_builder.spl:126`) renders with an **empty `arch`** and an `env` that
printed as a raw enum handle instead of text — i.e. `LlvmTargetTriple`'s scalar
fields are not surviving the way that function reconstructs them. That is a
text/enum rendering defect in the backend, unrelated to object layout. Not
investigated here.

## Reproduction

```
sh /home/ormastes/dev/simple-s3bisect/build/cyc/gdb_stage3.sh FIX1 GDBRUN1 1800
```

`FIX1/stage2-simple` is a stage2 built from a tree carrying blockers #2, #3 and
#4's fixes. Evidence retained under
`/home/ormastes/dev/simple-s3bisect/build/cyc/{FIX1RUN,GDBRUN1}`.

---

## Not re-measured 2026-08-17 (W4 bug-fixing wave) — left OPEN deliberately

This row's `.spl`-side fix is recorded as landed with RED/GREEN and a sabotage
check; the part left open is the underlying Rust-seed fail-open. That half was
NOT verified here, and no claim is made about it.

Why no measurement was taken: the observable is a SIGSEGV at ~394 s inside a
stage-3 self-host run, which requires rebuilt stage binaries. The staged binaries
present in this checkout are pre-fix artifacts carrying 169 `call 0` sites each
(measured 2026-08-17, see
`stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11`), so any crash
they produce cannot be attributed to a vtable field offset — a fault at `rip=0`
symbolizes to whatever function precedes the bad call, which is exactly how the
`emit_module_header` frame in this doc could arise without
`emit_module_header` being at fault. Distinguishing the two requires binaries
built from current source. Rebuilding was out of scope for this wave.

Left **OPEN**, unverified either way, per the wave rule that a wrong close loses
a real defect permanently. The next lane should re-take the backtrace only after
`sh scripts/check/check-no-call-zero.shs` reports `PASS` on the binaries under
test; otherwise the measurement is not interpretable.
