# riscv64 freestanding: invoking a `me` method on a class instance traps

## RESOLVED 2026-11-05 — root cause found in the HIR typer, fixed, verified in-guest

### Reproduction at tip (before the fix)

A minimal probe entry written to this record's specification
(`examples/09_embedded/simple_os/arch/riscv64/me_method_probe_entry.spl`,
committed with this update; booted by
`scripts/check/run-riscv64-text-probe-opensbi.shs` with
`ENTRY=.../me_method_probe_entry.spl`, real OpenSBI v1.4 fw_payload, `-bios`
only, QEMU 11.1.1) discriminated exactly as the 2026-08-31 probes predicted:

```
[meprobe] p1 static ctor + field read ok      <- static fn, known good
[meprobe] p2 me ping ok                       <- me method that IGNORES self: WORKS
<trap> scause=5 (load access fault) sepc=...first_id stval=0x8
```

So the receiver ABI is fine — a `me` method that never touches `self` runs.
The trap fires the moment a `me` method reads `self.entries` and the result
feeds a `+`.

### Root cause: lowercase `list<T>` erased to TypeId::ANY at HIR

`self.entries = self.entries + [entry]` lowered (MIR dump,
`SIMPLE_DUMP_MIR=1`, 3-line fixture) to:

```
FieldGet { ..., field_type: TypeId(14) }        # self.entries
ArrayLit { ... }                                # [entry]
BinOp { op: Add, left, right }                  # <- NATIVE INTEGER ADD
FieldSet { ..., value }                         # stores the SUM of two handles
```

`TypeId(14)` IS `TypeId::ANY`
(`src/compiler_rust/compiler/src/hir/types/type_system.rs:112`). The HIR type
resolver's `Type::Generic` arm special-cased `"List"` but NOT lowercase
`"list"` — which is the spelling the stdlib and every product module use —
so `list<T>` annotations fell through to `_ => Ok(TypeId::ANY)`
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`). Consequences in
MIR lowering (`mir/lower/lowering_expr_ops.rs`):

* both operands ANY -> `rt_any_add` (runtime tag-dispatch; arrays are not
  honestly handled there either, but the operands at least stay un-summed);
* one ANY + one concretely-typed array literal -> falls through to
  `MirInst::BinOp(Add)` -> cranelift emits a bare `add` on the two handles.

`me register` therefore stored `handle(entries) + handle([entry])` — a garbage
integer whose low tag bits are destroyed — into the field. The NEXT element
read (`rt_index_get` on the corrupted handle, or `ld` after it answers NIL)
faulted; in this probe, `first_id` loaded `id` at offset 8 from address 0
(`stval=0x8`). This is exactly the "self-receiving method call traps" signature
of this record — the receiver was innocent, as `m3f` suspected; the field
STORE was innocent too (the store itself never faulted); the corruption was
the array `+` mis-lowered to integer add, triggered by the ANY-typed
`self.entries` — which is also why no row of this gate had ever called a `me`
method that does real list work in-guest, while free-function array concat of
literals (`["a"] + ["b"]`, both operands concretely typed) worked.

### Fix

One-word change in the `Type::Generic` family dispatch:

```rust
"List" | "list" if args.len() == 1 => { ... HirType::Array { element, size: None } }
```

mirroring the bare-name fallback two screens up, which already maps bare
`list` to `Array`. After the fix the same fixture lowers to
`Call rt_array_concat` and the probe prints, in-guest:

```
[meprobe] p1 static ctor + field read ok
[meprobe] p2 me ping ok
[meprobe] p3 me self field read ok
[meprobe] p4 me register appended ok
[meprobe] p5 me find ok
[meprobe] p5b me find miss ok
PROBE_ME_METHOD_SIMPLEOS_RISCV64_DONE
```

Verified with a seed rebuilt from this branch
(`cargo build --release --bin simple`, exit 0) cross-compiling to
`riscv64gc-unknown-none-elf`. `text`-typed locals were unaffected (STRING is
resolved as a simple name), which is why string-heavy rows worked throughout.

### Regression guards added

* `scripts/check/check-hir-lower-list-generic-not-any.shs` — fail-closed, 4
  fatal selftest fixtures, verified genuinely RED against the pre-fix
  resolver source and GREEN with the fix.
* `test/01_unit/bugs/me_method_dispatch_registry_pattern_spec.spl` — pins the
  exact mcp dispatch shape (registry class, `me register` appending through
  `self.entries`, read-only `me find`, static constructors); 4/4 passing under
  `simple test --mode=interpreter` with the rebuilt seed.

### Environment caveat for reproducing this record's gates on other hosts

On a host WITHOUT `/home/ormastes/dev/pub/simple/...`, the components/probe
kernel links fail with undefined `rt_text_eq_any` at tip, because
`full_networking_runtime.c` includes the full freestanding runtime by absolute
path into that checkout. For the verification runs above, a scratch boot TU
providing exactly that one symbol was used and was NOT committed (on hosts
that have the external checkout it would duplicate-define the symbol). The
in-repo `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` cannot simply
replace the include: it diverged during the `88aac2ffe28` transplant and is
missing the `rt_boot_tcp_registry_*` core that `rt_net_socket_facade.spl`
links against. Tracked in
`freestanding_riscv64_for_in_array_yields_nil_after_first_element_2026-08-31.md`
(2026-11-05 section); the vendoring fix stays open there.

### Separate, still-open defect observed at tip (NOT this record's bug)

With the pre-fix seed, the full components gate
(`check-simpleos-riscv64-components-in-guest-opensbi.shs`) traps even earlier,
during module init (before the first `[components]` line): store access fault
in `rt_atomic_int_new` with the 8 MiB stack fully consumed and `rt_alloc`
returning 0 — a runaway init-time shape that needs its own record. The
minimal probe above avoids the heavy closure and isolates this record's
defect; whether the init trap is cured by the same fix is checked separately.

- **Status:** SUPERSEDED 2026-11-05 (PR #6954; independent review APPROVE-WITH-NITS, nits landed in follow-up)
Filed: 2026-08-31
Lane: `scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs` (mcp row)
Evidence: in-guest, real OpenSBI v1.4 `fw_payload`, `-bios` only. No `-kernel`, no `isa-debug-exit`.

## Symptom

The gate's `mcp` row traps. The CPU re-enters the entry (the two `[components]`
banner lines reprint) **without a fresh OpenSBI banner** — measured 1 OpenSBI
banner against 14,564+ entry banners — so it is a trap, not a machine reset.

## Localization (this is the new part)

Serial bisect probes were placed between every call in `mcp_component_row`. The
last line printed is `probe m3e`; `probe m4` never appears. Everything before
the trap works:

```
[mcp] probe m0 entering row
[mcp] probe m1 id_path_intern ok
[mcp] probe m2 DispatchEntry.echo ok
[mcp] probe m3 DispatchRegistry.new_for_test ok
[mcp] probe m3a local array concat returned      # ["a"] + ["b"]
[mcp] probe m3b elem=a
[mcp] probe m3b elem=b
[mcp] probe m3c array literal of DispatchEntry ok    # [entry]
[mcp] probe m3d DispatchEntry array concat ok        # [entry] + [entry]
[mcp] probe m3e first tool_name=echo                 # elem field read
<trap>
```

The only statement between `m3e` and `m4` is `reg.register(entry)`, whose whole
body (`src/lib/nogc_async_mut/mcp/dispatch.spl:89-90`) is:

```
me register(entry: DispatchEntry) -> ():
    self.entries = self.entries + [entry]
```

Every ingredient of that line is independently proven working in-guest by the
probes above: array literals of the class element type, array concatenation of
that type, and reading a field off an element.

**A second, discriminating probe settles which remaining operation is at
fault.** `probe m3f` was placed immediately before `register` and calls
`reg.find("no_such_tool_at_all")` — a `me` method on the same instance that
only READS `self.entries` (`for e in self.entries`) and stores nothing. It
prints nothing: `m3f` traps too, exactly like `register`.

So the defect is **invoking a `me` method on a class instance at all**, not the
field store. Note that no row of this gate had ever successfully called a `me`
method in-guest: devtool, caret and testrun reach their evidence through free
functions, static constructors, array `.len()` and plain field reads. The
static constructors (`DispatchEntry.echo`, `DispatchRegistry.new_for_test`) do
work (m2/m3) — those are `static fn`, which take no `self`. The failing shape
is specifically the `self`-receiving method call.

The original title of this record named the self-field STORE; that was the
leading suspect before `m3f` existed, and it is wrong. Kept here so the wrong
inference is not silently re-derived.

## What this rules out

* Not the `rt_value_int` untagged-index defect (PR #189) — that is fixed and
  live in this kernel (`slli a0,a0,0x3` in the linked `rt_value_int`).
* Not the `rt_index_get` text-subscript defect fixed alongside this record.
* Not array concatenation, in general or for this element type (m3a/m3d).
* Not the self-field STORE specifically — a read-only `me` method traps too (m3f).
* Not `static fn` constructors on the same classes, which work (m2/m3).
* Not entry construction, interning, or registry construction (m1/m2/m3).
* Previously ruled out by earlier lanes: defect C1 (module-global initialized
  from a call expression staying nil) and the closure ABI.

## Not yet located

There is no runtime helper to inspect: a grep of the whole riscv64 boot runtime
(`examples/09_embedded/simple_os/arch/riscv64/boot/*.c`, `*.inc.c`) for
`rt_field_set` / `rt_struct_set` / `rt_class_set` / `rt_field_get` returns
nothing, so class field access is direct-offset codegen. That places the next
step in the compiler's freestanding codegen for the `me`-method calling
convention — how the `self` receiver is passed — not in the C runtime.

Suggested next probe: the smallest possible reproduction, a two-line class with
one `me` method that only calls `serial_println` and touches no field. If that
traps, the receiver ABI is the whole story and the reproduction is small enough
to disassemble.

## Reproduce

```
sh scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs
grep -a -m 12 '\[mcp\]' build/os/riscv64_components/serial.log
```

The probes are checked in, in `toolchain_components_entry.spl`, so the serial
log names the last call that completed on every future run.

---

# P3 TRIAGE ADDENDUM (2026-11-11, lane boot8) — SUPERSEDED

Verdict: **SUPERSEDED — already fixed (PR #6954, 2026-11-05); re-verified by source + guard this lane.**

This doc's header records RESOLVED 2026-11-05 with in-guest verification. This
lane spot-checked at `work/p3-boot8-20261111` HEAD (`7d4140c1a6b3`):

- Source: the HIR type-resolver `Type::Generic` dispatch now special-cases
  lowercase `list`, at
  `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:669`
  (`"List" | "list" if args.len() == 1 => { ... HirType::Array ... }`), so
  `list<T>` no longer erases to `TypeId::ANY` and `self.entries + [entry]`
  lowers to `rt_array_concat`, not a native integer add.
- Guard: `sh scripts/check/check-hir-lower-list-generic-not-any.shs` →
  `selftest OK (4 fixtures)` + `PASS — 1 definition checked, lowercase list<T>
  resolves to HirType::Array (not TypeId::ANY)` (rc=0).

Host-limit note: in-guest re-run is not possible on this Windows host;
verification here is source-presence + guard. The in-guest proof (probe p1-p5b
green) stands from the 2026-11-05 section. The separate module-init trap
observed there is a different defect, out of this record's scope.
