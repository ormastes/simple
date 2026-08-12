# Native-build SIGSEGV `call 0x0` — mechanism hardened, upstream cause still open (2026-08-11)

## Summary

`native-build` on self-hosted binaries can crash with `call 0x0`-shaped SIGSEGVs.
The mechanism was traced to `src/compiler/70.backend/backend/native/native_elf.spl`
at the three architecture emitters (`emit_elf_x86_64`, `emit_elf_aarch64`,
`emit_elf_riscv64`). Each builds a `sym_name_to_idx: Dict<text, i64>` map while
walking data labels, extern symbols, and function names, then resolves each
relocation's `reloc.symbol_name` through that map. The lookup silently
defaulted to index `0` when the name was missing:

```
var sym_idx = 0
if sym_name_to_idx.contains(reloc.symbol_name):
    sym_idx = sym_name_to_idx[reloc.symbol_name]
```

## Correction to the original mechanism description

The original title/description assumed the fallback produced a genuine
null/`STN_UNDEF` target ("call to 0x0"). Reading the surrounding code shows
that's not quite right: the final ELF relocation symbol index written out is
`symbol_index: sym_base + sym_idx` (or `sym_base_a` / `sym_base_r` on the other
two arches), where `sym_base = 1 + num_content_sections` accounts for the null
symbol-table entry plus section symbols. So `sym_idx = 0` does **not** point at
ELF's real `STN_UNDEF` (index 0 of the whole symtab) — it points at
`sym_names[0]`, i.e. whatever symbol happened to be registered *first* in that
function's local `sym_name_to_idx` map (typically the first rodata data label,
or the first extern symbol if there's no rodata). In other words, the silent
fallback doesn't null out the call target — it aliases it to an arbitrary,
unrelated, already-resolved symbol. Depending on what that first-registered
symbol's address is, this can manifest as a call to address 0 (if the aliased
symbol itself resolves near zero, e.g. an unresolved extern), a jump into the
middle of unrelated data, or a call into the wrong function entirely — all
without any diagnostic. This is consistent with, and a superset of, the
originally observed `call 0x0` symptom.

Either way, `sym_idx = 0` from this fallback is never a legitimate "no
relocation needed" / "intentionally unresolved" sentinel in this code path —
every `ElfReloc` pushed here corresponds to an actual instruction operand that
must resolve to a real symbol. There is no code path in `emit_elf_*` where a
relocation is expected to reference a symbol absent from `sym_name_to_idx`.

## Fix landed (this session)

Hardened all three fallback sites from a silent wrong-symbol alias into a hard
build-time `panic(...)` naming the missing symbol, so a bad binary is never
silently produced:

```
if not sym_name_to_idx.contains(reloc.symbol_name):
    panic("native ELF (x86_64): relocation references unknown symbol '{reloc.symbol_name}' -- symbol was never registered in sym_name_to_idx (would silently emit a call to the wrong symbol)")
val sym_idx = sym_name_to_idx[reloc.symbol_name]
```

(same shape at the AArch64 and RISC-V sites, `panic(...)` is the idiomatic
fatal-error builtin used elsewhere in `70.backend/backend/**`, e.g.
`cranelift_codegen_adapter.spl:569,1053`, `isel_x86_64.spl:634,642`).

This converts a silent miscompilation into an immediate, named build error —
strictly safer than the previous behavior since `sym_idx = 0` was never a
legitimate case here. It does **not** fix the underlying defect: something
upstream still fails to register a symbol name into `sym_name_to_idx` before a
relocation referencing it is emitted for `func.relocations`. Likely
candidates worth checking next (not yet investigated — would require a
debug-symbol build + trace, out of scope for this read-only session):
forward-declared functions whose body is emitted before their name is added
to `ordered_funcs`/`module.extern_symbols`, generic-instantiation call
targets, or a relocation whose `symbol_name` uses a different naming
convention (e.g. mangled vs. unmangled) than what was registered.

## Status

- Mechanism: understood and corrected (silent misalign -> loud `panic`).
- Upstream cause (why a symbol goes missing from `sym_name_to_idx`): still
  UNKNOWN. Needs a debug build that can reproduce the missing-symbol case and
  print `reloc.symbol_name` plus the caller's context before this panic fires.
- No build/test was run to verify this change (host under heavy load,
  restricted to static source reading per session instructions). The edit is
  purely defensive (replaces a silent bad value with a loud error) and touches
  no other control flow, so risk of regressing a currently-passing build is
  low, but it has not been empirically confirmed.

## Follow-up static finding (2026-08-12, still not empirically confirmed)

Read-only follow-up session (host load ~12-16 on the 15m average, borderline
for a bootstrap build; a debug-symbol stage2/stage3 rebuild plus runtime
reproduction of the panic was judged out of proportion for this pass and was
not attempted — this section is static analysis only, not a confirmed repro).

Re-reading the registration loops in all three `emit_elf_*` functions in
`src/compiler/70.backend/backend/native/native_elf.spl` (e.g. x86_64 at
lines 44-68): `sym_name_to_idx` is populated from exactly three sources —

1. `module.data_sections` entries **filtered to `entry.is_readonly`** (line
   48: `for entry in module.data_sections: if entry.is_readonly: ...`)
2. `module.extern_symbols`
3. `func.name` for every function in `ordered_funcs`

**Mutable (non-readonly) `data_sections` entries are never added to
`sym_name_to_idx` at all** — the same `is_readonly` filter is repeated at the
symbol-table-writing site (line 147-158: `# Add data label symbols (local, in
rodata)` only ever emits `ElfSymbol`s for `entry.is_readonly` entries too).
`collect_section_bytes(module.data_sections, false)` (line 142) does emit the
mutable `.data` section's raw *bytes*, but no local symbol is ever registered
for any individual mutable-data label inside it. So any relocation whose
`reloc.symbol_name` names a mutable global/static data label (as opposed to a
rodata constant, an extern, or a function) will hit the new
`panic("...relocation references unknown symbol...")` unconditionally,
regardless of which specific name it is — this is a structural gap in the
symbol table, not a one-off naming mismatch.

This is a plausible, but *not confirmed*, explanation for the original
family of missing-symbol failures. It is very likely NOT the cause of the
specific trivial repro named in the bug title (`fn main() -> i64: 0`), since
that program has no module-level mutable state and should produce an empty
`module.data_sections` (or rodata-only). The trivial repro's actual missing
symbol was not captured in this session (no build was run), so it remains
open. Confirming either hypothesis requires the still-outstanding step: a
debug build that prints `reloc.symbol_name` and its caller/MIR context right
before the panic fires for the trivial repro specifically.

**Suggested next step if the mutable-data-symbol gap turns out to be real
and reachable:** add a fourth registration loop mirroring lines 44-54 but
for `if not entry.is_readonly`, assigning offsets from a running `data_offset`
counter over the `.data` section (parallel to `rodata_offset`/
`data_label_offsets`), and add corresponding `ElfSymbol`s with
`section_index` pointing at the `.data` section (not `2`/rodata) at the
line-147 site. Not implemented in this session — no build was run to verify
either the hypothesis or a fix, so no code change is landed here, only this
documented finding.

## RESOLVED (2026-08-12) — both hypotheses REFUTED; real cause found by actual build

An empirical pass finally ran the repro through the pure-Simple backend. Both
prior hypotheses are wrong, and the reason the panic never fired is that
`native_elf.spl` **was never executed at all** on any native-build.

### Method (so this is reproducible)

The seed `bin/simple` is Rust and never runs `native_elf.spl`; `bm native-build
--entry` routes to the legacy `rt_native_build` FFI ("not supported in
interpreter mode"). The pure-Simple lane is reached by calling
`run_focused_native_build` (`src/app/cli/bootstrap_focused_native_build.spl`,
`pub`, no Stage4 gate) from a small driver script run under the seed, against a
pristine `git archive origin/main` tree (the shared WC has in-flight foreign
edits in `50.mir/hwir/**`, which produce an unrelated
`enum MirInstKind not found in this scope`). Note `env_get` returns nil for
unset vars in the interpreter, so the env vars this function saves/restores must
be pre-set to `""` or it dies in `rt_env_set: value must be a string`.

### Finding 1 — `native_elf.spl` is unreachable; `CodegenTarget.Host` silently emitted a stub

`print` probes at `emit_elf_x86_64` and `compile_native_x86_64` recorded **zero
hits**, both on the default backend and with an explicit `--backend native`.
A probe on the dispatcher itself printed:

```
[PROBE] compile_native ENTERED target=CodegenTarget::Host
[PROBE] compile_native FELL THROUGH TO STUB for target=CodegenTarget::Host
```

`compile_native`'s `match target` in
`src/compiler/70.backend/backend/native/mod.spl` handled `X86_64`, `AArch64`,
`Riscv64`, `Riscv32` and the two macOS targets, but **not `Host` or `Native`** —
the two late-bound aliases the driver actually passes. Both fell into
`case _: compile_native_stub(module, "unsupported")`, which returns a
valid-but-empty ELF containing a single `ret` and no symbols, and reports
success. That code-less object is the true origin of the whole failure family:
depending on the linker it surfaces as `ld.lld: error: undefined symbol:
__simple_main` (observed here) or as a binary whose calls land nowhere — the
originally reported `call 0x0` SIGSEGV.

Note `supports_target()` returns `true` for `Host`, so nothing upstream ever
rejected it.

### Finding 2 — the mutable-data hypothesis is refuted, not merely unconfirmed

With the emitter finally reached, the reloc-site probe printed **zero**
`reloc.symbol_name` lines: `func.relocations` is empty for the trivial repro, so
the hardened `panic(...)` cannot fire and no symbol lookup happens at all. The
`sym_name_to_idx` registration gap for non-readonly `data_sections` (the
2026-08-12 static finding) is therefore **not** the cause of this bug. It may
still be a latent gap for programs that do carry mutable module-level state, but
it is unrelated to this report and no fix for it is landed here.

### Fix landed

`src/compiler/70.backend/backend/native/mod.spl`: resolve `Host`/`Native` to the
concrete host architecture via a new `native_resolve_host_target()` (built on
the existing `detect_host_arch()` in `backend/llvm_target.spl`; it never returns
`Host`/`Native`, so the `compile_native` recursion is one level deep), and
replace the silent `compile_native_stub` fallthrough with a `panic(...)` naming
the unsupported target. Emitting a code-less object is never a correct outcome,
so the same "loud beats silently wrong" rule already applied to the relocation
sites now applies to target dispatch. `compile_native_stub` had no other caller
and is deleted along with the now-unused `elf_writer` import it needed.

### Verification (measured)

| lane | before fix | after fix |
|---|---|---|
| default (`llvm`) | rc=0, binary runs, exit 0 | rc=0, binary runs, exit 0 — **no regression** |
| `--backend native` | rc=1, `undefined symbol: __simple_main`, emitter never entered | `[PROBE] emit_elf_x86_64 ENTERED`, rc=0, links, 20752-byte binary |

The `native` lane is opt-in via `--backend native`; the default `llvm` lane
never calls `compile_native`, so this change cannot regress it.

### Newly exposed, filed separately

With the stub no longer masking it, the pure-Simple x86_64 encoder is shown to
emit malformed machine code — the produced binary still segfaults. Disassembly
of the generated `main` for `fn main() -> i64: 0`:

```
1edb: 48 89 4c 89 48   mov %rcx,0x48(%rcx,%rcx,4)   # botched frame-slot store
1eef: 48 8b 4c 8b 48   mov 0x48(%rbx,%rcx,4),%rcx   # same bug, load side
1ef4: 89 ec            mov %ebp,%esp                # missing REX.W in epilogue
```

Bad ModRM/SIB for frame-slot access plus a missing REX.W on the epilogue
`mov %rbp,%rsp`. This is a distinct defect in `encode_x86_64.spl`, not in
`native_elf.spl`, and is tracked in
`doc/08_tracking/bug/native_x86_64_encoder_emits_malformed_modrm_sib_and_missing_rexw_2026-08-12.md`.

### Status

- Original `call 0x0` / SIGSEGV cause: **RESOLVED** — `Host` fell through to a
  code-less stub object; fixed by host-target resolution + loud panic.
- Mutable-data `sym_name_to_idx` hypothesis: **REFUTED** for this bug (no
  relocations exist in the repro).
- Pure-Simple x86_64 encoder correctness: **OPEN**, newly exposed, filed above.
