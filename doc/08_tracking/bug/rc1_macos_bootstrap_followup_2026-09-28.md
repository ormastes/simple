# RC1 macOS bootstrap follow-up

Release base: `0f0a2092585`. Platform: aarch64-apple-darwin, LLVM 18.

At `5bfd5024f5e`, a fresh Rust seed/runtime build and the canonical Stage 2
trust-root admission passed. The positional frontend smoke and struct receiver
check passed. The admitted parent produced a valid Stage 3 planner receipt.
Stage 3 passed memory-snapshot setup after the merged byte-span ABI repair,
then exited with 200 poisoned modules and 16,441 HIR diagnostics. The first
failures were ambiguous callable dependencies (`AsmTargetSpec`, `Span`, and
`Attribute`) reached through compiler facades.

The follow-up applies the source and regression changes from RC1 commits
`00627d2c6ed`, `445b8117ab5`, `68063a0965c`, and `a4915e9460f`: prefer explicit
named dependencies over competing glob routes; retain explicit declaration
origins; continue valid re-export routes after a missing indexed owner; and
re-register an imported binding after its function scope expires. These
backports require fresh native admission; no Stage 3 success is claimed here.

The portability gate also expected an obsolete literal DLL copy even though
the production authority deliberately carries a static runtime. The gate now
checks both archive spellings, and the authority test copies real GNU/MSVC
fixture tuples and verifies the static bytes. The source-snapshot fixture now
canonicalizes its temporary root so macOS `/var` aliases do not resemble an
external authority symlink. The pure-jj fixture explicitly selects
`--no-colocate`, because the installed jj now defaults to colocation.

The final local portability pass completed the authority, source-snapshot,
and pure-jj checks, then failed the unchanged `FreeBSD full execution wiring
missing` structural assertion. The gate's three-run cap was reached; no full
portability PASS is claimed. Its log is
`/private/tmp/rc1-portability-final-20260928.log`.

Verification performance: the local guard-wiring checker spent over eight
minutes in `/usr/bin/grep -r -I -l -F -f` over the source tree. That redundant
local scan was terminated; its self-test had passed. The canonical CI wiring
check passed after commit `5bfd5024f5e`. The checker hardcodes BSD grep on this
host despite GNU grep being installed; tool selection or scan scope should be
addressed in a separate measured guard-performance change.

Raw logs are retained in the isolated worktree's `build/bootstrap/logs/` and
the session's `/private/tmp/simple-rc1-*` files. They are local evidence,
not published release qualification receipts.

## 2026-09-29: wrong receiver layout in the admitted Stage 2

Stage 2 passed at `0ec857786ae`, but its Stage 3 driver rejected MC/DC budgets
with owner `8606133032844533876` and global `7310601557487281518`. In little
endian these are `t the ow` and `ner byte`, fragments of the error message.
Disassembly proves an out-of-bounds field layout: `CompilerConfig.default`
allocates 112 bytes, and `CompilerConfig.from_env` accesses the budgets at
offsets `0x50`/`0x58`. `CompileContext.create` instead reads and writes those
fields at `0xb0`/`0xb8`, the offsets in `CompileOptions`.

The driver now explicitly imports `CompilerConfig` and annotates the local
receiver. This addresses the bootstrap producer's loss of the imported static
call's return type in the large driver import graph. General inference remains
a compiler bug; no environment or budget-value workaround is being admitted.
The focused `driver_config_layout_spec.spl` exercises the production context
with inherited budgets, CLI overrides, and invalid-budget rejection.

A seven-module standalone probe with an inferred receiver passed on the old
producer. It does not reproduce the large driver graph's collision and is not
regression evidence. Native driver qualification is required for this change.

The rebuilt production driver object (`5cf0424b7359fb58.o`, cache scope
`7c9fc156f4d5496a`) now stores the two configuration budgets at `0x50`/`0x58`.
Before/after disassembly is preserved under
`build/native_probe/config-layout/`. This proves the receiver layout repair;
the bootstrap admission and Stage 3 checks remain separate gates.

Stage 2 admission passed with the receiver annotation. Stage 3 passed the
budget check and parsed all 717 modules, but HIR stopped advancing at module 9
(`driver_riscv_gen2_product`). A native sample found repeated imported-method
registration with a peak physical footprint of 20.2 GB. The process was stopped
with SIGTERM; this is not a completed HIR result. The sample and log are in
`build/native_probe/config-layout/`.

A bounded LLDB diagnostic launch exposed a second wrong layout before HIR:
`CompileOptions` constructs its budgets at `0xa0`/`0xa8`, while the driver reads
`0xb0`/`0xb8` through its facade import. This yielded owner `53738125249` with
ASLR disabled. Driver boundaries now import the concrete `CompileOptions`
declaration, and both bootstrap call sites annotate their options receivers.
These additions still require native admission; the imported-method memory
growth remains a separate unresolved observation.
