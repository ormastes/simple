# Stage-3/stage2 self-hosted `native-build` SIGSEGV root cause: `call 0x0` baked into the binary (unpatched relocation)

- **Date:** 2026-08-11
- **Status:** OPEN — root cause diagnosed, no fix landed
- **Scope:** `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
  `bootstrap/stage2/simple` (and by the same mechanism, every self-hosted
  candidate `simple_compiler_select` currently rejects on the second probe
  rung). Relates to
  `doc/08_tracking/bug/simple_compiler_select_promotes_stage2_binary_without_run_subcommand_2026-08-06.md`,
  which documented the SIGSEGV's *existence* (rc=139 on `native-build`) but
  not its cause.

## Context

`simple_compiler_select`'s second probe rung
(`scripts/lib/simple-compiler-select.shs:189`) runs a real
`native-build --entry p.spl --source . -o probe_bin` against a trivial
one-line fixture (`fn main() -> i64:\n    0\n`). This is the "capability
probe" referenced by the task. On this host it SIGSEGVs (rc=139) on both
`bootstrap/stage3/x86_64-unknown-linux-gnu/simple` and
`bootstrap/stage2/simple`, which is why the selector rejects them and falls
through to weaker candidates. This blocks any lane that needs a genuine
self-hosted `native-build`, including the SimpleOS real-firmware harness.

## Reproduction

```sh
mkdir -p /tmp/probe && cd /tmp/probe
printf 'fn main() -> i64:\n    0\n' > p.spl
/home/ormastes/dev/pub/simple/bootstrap/stage3/x86_64-unknown-linux-gnu/simple \
    native-build --entry p.spl --source . -o probe_bin
# -> Segmentation fault (core dumped), exit 139
```

Confirmed on both `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` and
`bootstrap/stage2/simple` (same binary size, 3,464,072 bytes, both dated Aug
10 12:09 — likely the same build artifact deployed to two paths).

No core file was written (host `core_pattern` pipes to `apport`, which does
not deposit a readable core here). Used `gdb --batch -ex run -ex bt -ex
"info registers"` instead — this is a LIVE run, not a stale-core artifact.

## Crash evidence

```
Program received signal SIGSEGV, Segmentation fault.
0x0000000000000000 in ?? ()
#0  0x0000000000000000 in ?? ()
#1  0x000000000040465e in ?? ()
#2  0x00000000004025f5 in ?? ()
#3  0x00007ffff7c2a1ca in __libc_start_call_main (...)
#4  0x00007ffff7c2a28b in __libc_start_main_impl (...)
#5  0x00000000004024f5 in ?? ()

rip            0x0                 0x0
rax            0x13
```

`rip=0`, frame #1 return address `0x40465e`. Disassembling the call site
(`objdump -d --start-address=0x404600 --stop-address=0x404680`):

```
404650: mov    (%rsp),%r13
404654: mov    0x10(%rsp),%rdi
404659: call   0 <ftell@plt-0x402030>     ; e8 a2 b9 bf ff
40465e: mov    %rax,%r14                  ; <- return address on stack (frame #1)
```

## Root cause

This is **not** a runtime null-pointer dereference (no register holds 0
being called through indirectly — `rip` is 0 because the CPU already
executed a *direct* `call` whose encoded target IS address `0x0`). The
instruction bytes `e8 a2 b9 bf ff` are a relative `CALL rel32`; objdump
resolves the target purely arithmetically to `0x0` and mislabels it via the
nearest preceding symbol (`ftell@plt-0x402030`, a symbolization artifact —
this is not really a call to a `ftell` variant).

A direct `call` with a literal zero target address baked into the `.text`
section at build time means: **whatever code path emitted this call
instruction (during the self-hosted binary's own build/link) computed a
callee address of zero and encoded it into the relative-offset immediate
field, instead of the intended function's real address.** This is
characteristic of an unpatched/never-resolved relocation — a symbol whose
address the linker or the self-hosted native codegen's own relocation-fixup
pass failed to fill in, leaving the placeholder `call rel32` field at its
default (zero-relative, i.e. absolute `0x0`) value.

The call is unconditional and unguarded, so any code path through this
region of `main()` in the trivial fixture's compiled output hits it
deterministically — consistent with the 100%-reproducible SIGSEGV on every
`native-build` invocation the selector's probe rung has observed.

**What's NOT yet established** (would need matching this address back to a
known .spl source function, e.g. via a debug/symbol build of the same stage,
which wasn't available in the tree): which specific self-hosted routine
emits this call, and whether the unresolved symbol is a runtime helper
(`rt_*`), a libc function, or a self-referential linker/build-time construct.
The surrounding disassembly (repeated calls at `69cea0`/`69a380`/`69e94c`,
consistent stack layout) looks like inlined string/IO helper glue -- consistent
with `native-build`'s own file-output pipeline (writing `probe_bin`), which
would explain why `check p.spl` (no file output) is unaffected but
`native-build ... -o probe_bin` is not.

## Why no fix was attempted here

Root-causing the *exact* emitting call site requires a symbol-table-preserving
(unstripped, or matched to a `.map`/debug) build of the same commit that
produced these two binaries, which isn't available in this tree, plus
correlating against `src/compiler/70.backend` relocation/link-fixup code.
Per task scope, this is investigation-only: no rebuild/redeploy of
`bin/simple` or the staged binaries was performed, and no source-level fix
was identified with enough confidence to land safely without that
correlation step.

## Suggested next step

Rebuild stage2/stage3 with debug symbols retained (or add
`--emit-relocations`-style diagnostics to the self-hosted linker/backend) and
re-run this exact repro under gdb with symbols, to identify which relocation
record was never patched. Prime suspects: the self-hosted backend's own
symbol-resolution/link-fixup pass under `src/compiler/70.backend/`.

---

## FAMILY RESOLUTION 2026-08-17 (W4 bug-fixing wave) — the emitting code path IS known, and the source fix already landed

The "what's NOT yet established" question above (which routine emits the
`call 0`) is answered by a sibling row filed two days earlier:
`doc/08_tracking/bug/stage2_native_build_link_undefined_method_symbols_2026-08-09.md`.

That doc's "Corrected root cause" section states the mechanism exactly: the Rust
seed's LLVM backend **mints an unmangled external for a call target it could not
resolve** (bare method leaves such as `starts_with`, `split`, `replace`,
`substring`, `rfind`, `char_code_at`, plus `TaskState.is_terminal`). It then
records the two possible outcomes:

| tree | what happens to the unresolvable call |
|---|---|
| with `36673b6b6a3` | undefined symbol → link fails loudly, fail-closed |
| without `36673b6b6a3` | binds to absolute `0` → binary builds, then SIGSEGVs with `rip=0` |

and it names the count in the pre-fix binary: **169 direct `call 0` sites**.

### Measurement on this host, 2026-08-17

Reproduced this doc's repro verbatim against the in-repo staged binary
(`/mnt/data/worktrees/simple-main`, both staged binaries 3,464,072 bytes):

```
$ printf 'fn main() -> i64:\n    0\n' > p.spl
$ bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build --entry p.spl --source . -o probe_bin
Segmentation fault (core dumped)   # rc=139
```

Then the fail-closed detection channel that exists for exactly this class:

```
$ sh scripts/check/check-no-call-zero.shs \
    bootstrap/stage3/x86_64-unknown-linux-gnu/simple bootstrap/stage2/simple
call-to-zero: bootstrap/stage3/... has 169 site(s)
call-to-zero: bootstrap/stage2/simple has 169 site(s)
FAIL — 338 call-to-zero site(s) across 2 binary/binaries
```

**169 per binary — the exact figure the 08-09 doc reports for the pre-fix
tree.** The first site is at `404659` with bytes `e8 a2 b9 bf ff`, byte-for-byte
identical to the crash-site disassembly quoted earlier in this document. These
two staged binaries are therefore artifacts of a tree that predates
`36673b6b6a3`; they are not evidence about current source.

### Current source is fail-closed (verified by inspection)

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:3207-3225` — an
  unresolvable `GlobalLoad`/`GlobalStore` target now returns
  `CompileError::semantic("llvm global load referenced undeclared symbol ...")`
  rather than minting a global. No fabrication path remains there.
- `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` —
  `freestanding_unresolved_mode()` defaults to `DeferToLinker`/`StrictPrecheck`
  and **never** enters `EmitStubs` under `SIMPLE_NO_STUB_FALLBACK=1`; the one
  remaining `EmitStubs` path is gated by `check_fabricated_stub_ratchet` against
  a per-entry baseline, and `stale_module_move_report` hard-errors *before* the
  mode match on any undefined `lib__*`/`os__*` symbol whose bare name is defined
  under a different module prefix.
- `src/compiler/70.backend/backend/llvm_native_link.spl:1814,2647,2666` —
  `simpleos_undefined_simple_module_symbols` + channel 3 refuse the freestanding
  link on any newly-fabricated pure-Simple symbol.

### Status change

**RETIRED as a source defect; re-scoped to an artifact-staleness item.** No
source fix is outstanding for this row. What remains is a *rebuild*: the staged
`bootstrap/stage2/simple` and `bootstrap/stage3/.../simple` in this checkout must
be rebuilt from current source, after which
`sh scripts/check/check-no-call-zero.shs <new binaries>` must report `PASS`. That
rebuild was explicitly out of scope for this wave (redeploying `bin/simple` /
`bin/release/**` clobbers ~16 concurrent lanes), so the row is left open ONLY on
that gate, with the acceptance criterion now mechanical.

### Family

Rows collapsed into one cause — "an unresolvable callee is materialised as a
weak/undefined symbol that links to address 0, so the call returns zero or
faults instead of failing the build":

- `stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11` (this row)
- `stage2_native_build_link_undefined_method_symbols_2026-08-09` (the fix,
  `36673b6b6a3`; measured 34 → 0 undefined refs, Stage 2 links)
- `bytespan_starts_with_dropped_from_kernel_closure_weak_nil_stub_2026-07-28`
  (same shape via the *stub fabricator* rather than the linker; D1 cache key
  ungated at `native_project/mod.rs:910`, D2 guards as listed above)
- `freestanding_entry_module_constants_zero_stubs_2026-07-11` (entry-module
  `val`s becoming weak `xor eax,eax; ret` bodies — the same fabricator)
- `native_build_llvm_explicit_return_lost_every_call_returns_zero` — the
  "every call returns zero" symptom is the *observable* of this family whenever
  the fabricated body is reached rather than the null address.
