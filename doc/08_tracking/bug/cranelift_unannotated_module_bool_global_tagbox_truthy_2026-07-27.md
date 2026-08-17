# Un-annotated module-level `val x = false` is stored tag-boxed (19) and reads TRUTHY

- **ID:** cranelift_unannotated_module_bool_global_tagbox_truthy_2026-07-27
- **Status:** OPEN — root-caused, reproduced at object level, not fixed
- **Severity:** high (silent wrong-branch; no diagnostic, no crash)
- **Backend:** Cranelift. LLVM backend not tested (see Unverified).
- **Trigger config:** `--entry-closure --mode dynload --emit-archive --target x86_64-unknown-none --opt-level=none`

## Symptom (verbatim field report)

> OBSERVATION (verified in the SimpleOS x86_64 guest, cranelift,
> `--target x86_64-unknown-none`): I added a module-level constant to
> `src/os/services/vfs/vfs_boot_init.spl`:
>
> ```
> val _VFS_BOOT_TRACE = false
> ...
>     if _VFS_BOOT_TRACE:
>         serial_println("[vfs-init] scalar scratch read begin cluster={cluster}")
> ```
>
> In the guest, the gated lines PRINTED ANYWAY — 3,386 of them. So
> `_VFS_BOOT_TRACE` evaluated TRUTHY despite being initialised to `false`. The
> gate compiled fine and the string is present in the ELF. Replacing the global
> with a function (`fn _vfs_boot_trace_enabled() -> bool: false`) is what I am
> now testing as the workaround.

## Root cause

`CommonBackend::declare_globals` bakes the module-global initializer into a data
object. `src/compiler_rust/compiler/src/codegen/common_backend.rs:1607`:

```rust
let init_val = if *ty == TypeId::BOOL && (raw_init & 0b111) == 0b011 {
    (raw_init >> 3) & 1
} else {
    raw_init
};
```

The untag is **gated on the declared type being `TypeId::BOOL`**. For
`val x = false` with **no type annotation** the global's `TypeId` is not `BOOL`,
so the untag is skipped and the *tag-boxed* constant is written verbatim:
`TAG_SPECIAL 0b011 | payload<<3` → `false = 0b10011 = 19`, `true = 0b1011 = 11`.

The consumer (`if x:`) loads the slot as a raw i64 and branches on
`test %r8,%r8` — no untag. 19 is non-zero, so `false` takes the *then* branch.
`true` accidentally works because 11 is also non-zero. The comment at
`common_backend.rs:1598-1606` already documents this exact hazard; the guard is
simply too narrow.

## Evidence (object level, reproduced 2026-07-27)

Oracle (fresh cache, stage3, cranelift, freestanding, `--emit-archive`), entry:

```simple
val _A_ANNOT: bool = false
val _B_BARE      = false
val _C_TRUE      = true
val _D_TRUE_ANNOT: bool = true
```

`objdump -s -j .rodata.subsection mod_0.o`, in symbol order:

| symbol | bytes | value | correct? |
|---|---|---|---|
| `_A_ANNOT` (`: bool = false`) | `00 00 ...` | 0 | YES |
| `_B_BARE` (`= false`) | `13 00 ...` | **19** | **NO — truthy** |
| `_C_TRUE` (`= true`) | `0b 00 ...` | 11 | truthy by luck |
| `_D_TRUE_ANNOT` (`: bool = true`) | `01 00 ...` | 1 | YES |

Consumer disassembly (`spl_main`, separate oracle):

```
movabs $0x0,%r8      ; R_X86_64_64  <module>___GT_TRACE
mov    (%r8),%r8     ; full 8-byte load, no untag
test   %r8,%r8
je     ...           ; 19 != 0  =>  branch NOT taken  =>  body runs
```

Bare `val _GT_NUM = 7` stored as raw `07` — integers are unaffected.

## `__module_init_*` — the strong prior was WRONG for this config

`doc/08_tracking/bug/cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`
states cranelift "rejects non-scalar statics, never runs `__module_init_*`".
That is **not** what this configuration does. Verified in the emitted archive:

- `__module_init_<module>` **IS** emitted (weak FUNC, in `mod_0.o`) — it
  initialises **text/heap** globals only (`rt_string_new_literal` → store to a
  `.bss.subsection` slot). Scalars are not in it; they are statically baked.
- `__simple_call_module_inits` **IS** emitted with a real body, in a generated
  `_init_all.o` inside the archive, and it *does* contain the weak-guarded call:
  `mov $0x0,%eax; test %rax,%rax; je ...; jmp <__module_init_...>`.
- Emit site: `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:812`
  (`generate_init_caller`), reached for archives at
  `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1027-1028`.
- Symbol naming: `src/compiler_rust/compiler/src/codegen/common_backend.rs:470`
  (`module_init_symbol`), preserved through mangling at `common_backend.rs:1191`.
- Guest-side call site: `src/os/kernel/arch/riscv64/boot.spl:24,72`;
  `examples/09_embedded/simple_os/arch/common/baremetal_startup_handoff.c:4`;
  `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:9045,9270`.

So **this bug is not a missing module-init**. It is a wrong static initializer
byte. The two must not be conflated.

## Secondary hazard (INFERRED, not verified)

`src/os/libc/simpleos_simple_runtime.c:231` defines an **empty**
`void __simple_call_module_inits(void) {}`, packaged into
`libsimple_runtime_compat.a` by `src/os/port/llvm/sysroot.shs:127-130`. If a
guest link resolves the call to that strong empty definition instead of the
archive's `_init_all.o`, **text and aggregate module globals silently stay nil**
while scalars still work. Link-order dependent. Not confirmed against a real
guest link — do not treat as established.

## Blast radius

Module-level `val`/`var` at column 0, counted 2026-07-27:

| | `src/os` | `src/lib` |
|---|---|---|
| total module-level `val`/`var` | 4,305 | 7,314 |
| **bare `= false`** (BROKEN) | **0** | **38** |
| bare `= true` (wrong bytes, right behaviour) | 0 | 5 |
| annotated `: bool` (safe) | 72 | 100 |
| bare numeric (safe) | 19 | 1,485 |
| bare text (module-init path, different risk) | 93 | 397 |

- **Guest-reachable damage today: zero.** `src/os` currently has no bare-bool
  module global. The defect is **latent** and fires the moment someone adds one
  — exactly what happened here.
- All 38 `src/lib` cases are `var` in host-side tooling
  (`mcp_sdk/`, `mcp/`, `lsp/`, `test_runner/`, `llm/`, `aop_debug_log.spl`,
  e.g. `var g_log_enabled = false`, `var REGISTRY_BUILT = false`,
  `var LSP_INITIALIZED = false`). The same `declare_globals` path serves hosted
  cranelift builds, so each of these reads **true** until first assignment.
  Not measured on a hosted binary — flagged, not proven.
- Text globals are a *different* mechanism (`__module_init_*` + `.bss`) and are
  not affected by this tag-box bug.

## Workarounds

1. **Annotate the type** — `val _VFS_BOOT_TRACE: bool = false`. VERIFIED
   correct at object level (`00` bytes). Cheapest, keeps the global.
2. **Function constant** — `fn _vfs_boot_trace_enabled() -> bool: false`.
   **SOUND.** Verified: the emitted code loads an untagged byte
   (`movzbq`) and never touches the tag-boxed data slot. Function returns go
   through the native `bool` ABI, which is 0/1, not tag-boxed. This does not
   share the hazard.
3. Do **not** rely on bare `= true` "working" — it stores 11, so any code that
   compares the global against a real `true` (1), passes it to a runtime call
   expecting 0/1, or serialises it will still be wrong.

## Proper fix

In `common_backend.rs:1595-1615`, widen the untag so it does not depend on the
declared `TypeId`:

- Untag whenever `(raw_init & 0b111) == 0b011` **and** the payload is a boolean
  special (i.e. the module-pass captured a tag-boxed bool), regardless of whether
  the global's inferred type is `BOOL` or `ANY`; or
- better, stop lowering an un-annotated `= false`/`= true` module binding to
  `ANY` in the first place — infer `BOOL` in the module pass so the existing
  guard fires. This also fixes any other consumer that assumes a raw i8 load.

Either fix needs a regression fixture in
`scripts/check/native-smoke-matrix.shs` asserting the emitted data bytes for all
four shapes (`bare/annotated` × `false/true`), on **both** backends, because the
failure is silent and byte-level.

## Reproduce

```bash
cat > /tmp/gt.spl <<'EOF'
val _A: bool = false
val _B = false
fn main():
    if _B:
        print("BUG")
EOF
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB="$PWD/src" SIMPLE_ALLOW_FREESTANDING_STUBS=1 \
  build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build \
  --source src/lib --source src/os --timeout 600 --backend cranelift \
  --cpu x86-64-v1 --opt-level=none --log off --cache-dir /tmp/gtcache \
  --mode dynload --entry-closure --entry /tmp/gt.spl \
  --target x86_64-unknown-none --emit-archive -o /tmp/gt.a
mkdir -p /tmp/gtx && cd /tmp/gtx && ar x /tmp/gt.a
objdump -s -j .rodata.subsection mod_0.o     # _B slot reads 13 (=19), not 00
```

## Unverified

- LLVM backend: not exercised. `llvm/backend_core.rs:391` has its own
  module-init generator; whether it shares the tag-box bug is unknown.
- Non-x86_64 targets (riscv32/riscv64/aarch64): assumed identical since the
  defect is in target-independent `declare_globals`, but not measured.
- The empty-`__simple_call_module_inits` link hazard above.
- Whether the 38 `src/lib` host-side `var ... = false` globals actually
  misbehave in a shipped hosted binary.

## Cross-links

- `doc/08_tracking/bug/cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`
  — its "cranelift never runs `__module_init_*`" claim is contradicted by the
  archive evidence above for the entry-closure/emit-archive config; that doc
  should be amended.
- `doc/08_tracking/bug/native_module_val_globals_2026-07-23.md` — cross-import
  module globals broken even for scalars. **Different bug**: that one is about
  cross-module *resolution*; this one is same-module and about the *initializer
  byte*. Both must be fixed.
- `doc/08_tracking/bug/cranelift_module_global_initializer_arity_2026-07-19.md`
  — earlier module-init work; established the init-caller path this doc verifies.
- `doc/08_tracking/bug/cranelift_runtime_initialized_float_global_2026-07-19.md`
  — sibling initializer-encoding defect for floats.
- `doc/08_tracking/bug/llvm_backend_missing_module_init_heap_globals_2026-06-15.md`
  — the LLVM-side analogue of the heap/text module-init mechanism.
- Memory topic `project_module_global_mir_lowering_2026-07-25`.

## Update 2026-08-17 — ALREADY FIXED; prior "OPEN" re-verification inspected the wrong layer

**Verdict: fixed in-tree. Not reproducible.**

The 2026-08-17 triage re-verified this as OPEN by finding the `TypeId::BOOL` gate
still present in `codegen/common_backend.rs` (now line 1726, doc cites 1607 —
line drift only). That gate is real, but it is **not** where the fix lives, and
by its own comment it is a deliberate no-op backstop.

The fix moved **upstream** to HIR module lowering:
`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:169`

```rust
fn bool_global_init(val: bool) -> i64 { i64::from(val) }
```

It is applied **unconditionally, with no TypeId gate**, at all three global
initializer sites — statics (:676), consts (:734), and module-level locals
(:821). Bool globals are therefore captured as raw `0`/`1` for *every* declared
type, annotated or not, so the tag-boxed `19`/`11` values this bug describes are
never written in the first place. Its doc-comment names this bug file directly
and states the intent: "Emitting raw 0/1 here fixes every backend at once."

Why the backend gate correctly stays gated on `TypeId::BOOL` (i.e. do **not**
"fix" it by removing the gate): for an un-annotated slot a tagged `true` (11) is
indistinguishable from the integer initializer `val x = 11`, so value-sniffing
there would silently corrupt integer globals — trading this bug for a worse one.

Consistency check (weak, wrong lane, recorded for completeness): a hosted probe
with a module-level `val g = false` prints `ok: falsy` on both jit and
interpreter. This does NOT exercise the cranelift `--target x86_64-unknown-none
--emit-archive` lane the field report used, so it is corroboration only; the
source evidence above is the basis for this verdict.

**Action:** status corrected OPEN -> FIXED. Lesson for triage: verifying a fix by
inspecting the layer the bug doc happens to name can produce a false OPEN when
the fix landed upstream of it.
