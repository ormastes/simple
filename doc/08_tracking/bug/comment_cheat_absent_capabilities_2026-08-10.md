# Comment-cheat vacuity family #2 — ABSENT capabilities (stream Q5, 2026-08-10)

Specs whose source-scanning needle matches ONLY a comment in the product source.
This record covers the **ABSENT** subset: sites where the capability the spec
claims to prove **does not exist in code at all**. The vacuous needle was the
only thing holding the gate green.

Companion enumeration: `doc/08_tracking/test/comment_cheat_spec_census_2026-08-09.md`.

## Enumeration (re-derived, two independent cross-checks)

| method | raw | deduped |
|---|---|---|
| A — needle paired with nearest preceding product-path literal in the spec | 105 | 60 |
| B — needle searched across **every** product path the spec references (order-independent) | 176 | 119 |
| **A ∩ B (high confidence)** | — | **46 sites / 30 specs** |

A-only (14) are pairing artifacts: the needle is real code in a *different* file the
spec also reads. B-only (73) are needles absent from the paired file but present as a
comment elsewhere — weaker evidence, excluded.

### Scanner correction — the prior census over-counted

The 2026-08-09 census (and the first pass of this one) treated any line whose
trimmed form starts with `*` as a comment. That is a C-family block-comment
continuation rule and it is **wrong for shell**, where `*rust-built*|*rust*seed*)`
and `*) echo "error: ..."` are `case` arms, i.e. executable code. It also
mis-scored `#include` / `#define` in `.c` files as comments when they are
preprocessor directives. Restricting `*`-continuation to `.c/.h/.cpp/.js/.ld/.rs`
and treating `#` in C-family files as code removed **16 false hollow sites**,
including every `simpleos_wm_fullscreen_evidence`, `macos_metal_live_evidence`,
`gui_showcase_perf_artifact_provenance`, `fork_alloc_tracking` and
`thread_alloc_tracking` row. Those gates are sound; the scanner was not.

## Classification

| verdict | sites |
|---|---|
| REAL — capability exists, needle merely anchored on a comment | 31 |
| **ABSENT — capability does not exist (defects below)** | **7** |
| AMBIGUOUS — asserting the comment is deliberate, or the needle is not an assertion | 8 |

## ABSENT — genuine product defects

### D1. ARM64 EL0 handoff concurrency contract is unimplemented (3 sites)

Spec: `arm64_user_exit_return_contract_spec.spl`.
Product: `src/os/kernel/arch/arm64/user_entry.spl:68-69`

```
    # ponytail: one active EL0 handoff per CPU; PID-keyed recorded handoffs and
    # nested kernel resume frames are required before concurrency is enabled.
```

All three needles — `one active EL0 handoff per CPU`, `PID-keyed recorded handoffs`,
`nested kernel resume frames` — match only this deferral comment. The comment states
outright that these properties are *required before concurrency is enabled*, i.e. they
are **not** present. A repo-wide scan of all 58,860 tracked `src/`+`scripts/` files
finds no `handoff_by_pid` / `pid_keyed` / `handoffs_by_pid` symbol of any kind. The
only live entry point is `rt_arm64_enter_recorded_user_live()`, defined nowhere but
`user_entry.spl` itself.

The spec therefore asserts a per-CPU/per-PID handoff contract that no code implements,
and passes because the deferral note happens to contain the words.

**Unblock:** implement per-CPU single-active-handoff tracking and PID-keyed handoff
records, then re-anchor the spec on those symbols. Until then the spec must be RED.

### D2. `rt_syscall_dispatch` — the named live ring-3 syscall path exists nowhere (1 site)

Spec: `simpleos_green_hardware_handoff_blocker_spec.spl`.
Product: `src/os/kernel/ipc/syscall.spl:206`

```
# production". The live ring-3 path is syscall_entry.s -> rt_syscall_dispatch
```

Scanned every tracked file under `src/` and `scripts/` (xargs-fed, with a positive
control needle to prove the scan ran). `rt_syscall_dispatch` occurs **twice in the
entire product tree, and both are comments**:

- `src/os/kernel/ipc/syscall.spl:206`
- `src/os/kernel/arch/x86_64/cpu.spl:126` — *"dispatcher `rt_syscall_dispatch` in
  baremetal_stubs.c"*

There is no definition, no `extern fn` declaration, and no call site. `syscall_entry.s`
does not exist under `src/os` either — the only file of that name in the repo is
`examples/09_embedded/simple_os/arch/x86_64/boot/syscall_entry.s`, which is example
code, not the product.

This is the same shape as the dead GHDL wrapper found in family #1: two comments
describe a live path by name, and a source-grep spec certifies the path exists by
matching the prose that describes it.

**Unblock:** either implement `rt_syscall_dispatch` and wire `syscall_entry.s` into
`src/os`, or correct both comments to name the path that actually runs — and re-anchor
the spec on that symbol.

### D3. ARM/RISC-V QEMU boot lanes have no real-firmware proxy (3 sites)

`.claude/rules/board-runnable.md` requires every QEMU-developed lane to boot via a
real-firmware proxy — OVMF pflash (x86_64), OpenSBI (riscv), EDK2/AAVMF (aarch64) —
and forbids QEMU `-kernel` pass semantics. These three specs anchor on comments that
**document the violation**:

| spec | needle | product | evidence |
|---|---|---|---|
| `boot_smoke_spec.spl` | `-kernel` | `src/os/kernel/arch/arm64/linker.ld:4` | `RAM starts at 0x40000000, kernel loaded by QEMU -kernel flag.` |
| `qemu_runner_spec.spl` | `-kernel` | `src/os/kernel/arch/arm32/boot.spl:12,38` | `On QEMU virt, the kernel is loaded directly with -kernel flag.` |
| `riscv32_boot_qemu_spec.spl` | `RISC-V 32` | `src/os/kernel/arch/riscv32/linker.ld:1` | `QEMU virt machine, direct M-mode boot` / `Kernel loaded at 0x80000000 with -bios none.` |

`-bios none` on riscv32 means **no OpenSBI**; direct `-kernel` on arm32/arm64 means no
EDK2/AAVMF. The aarch64 EFI-stub gap is already acknowledged in `board-runnable.md`;
the arm32 and riscv32 lanes are not, and neither is the fact that specs named
`boot_smoke` / `qemu_runner` / `riscv32_boot_qemu` currently certify these lanes by
matching the comment that admits the bare-boot.

Related, already filed for rv64:
`doc/08_tracking/bug/riscv_qemu_lanes_boot_bare_kernel_without_opensbi_2026-08-09.md`.

**Unblock:** boot arm32/arm64 via EDK2/AAVMF pflash and riscv32 via OpenSBI, keep a
documented physical-board build+boot path per `board-runnable.md`, then anchor these
specs on the firmware-proxy invocation rather than on the memory-map prose. Until then
the specs must be RED and must not be read as board-runnable evidence.

## AMBIGUOUS — not defects, do not "fix"

- `sugar_plugin_spec.spl` (2): the `[STATIC-NEXT]` contract asserts marker **comments**
  exist at named sites. Asserting a comment *is* the contract.
- `evalops_export_and_text_at_spec.spl` (3): an `it` block explicitly named
  "documents text .at as a deliberate divergence from the seed" pins the rationale
  comment on purpose.
- `stdlib_intensive_spec.spl` (2): the needles (`/`, `name`) are spec-internal control
  flow (`if line.contains("name"):  # Skip header`), not assertions.
- `mcp_lsp_tools_spec.spl` (1): the spec builds the string under test inside itself and
  asserts against it, never reading the product. A worse defect than comment-cheating,
  out of scope here — it needs rewriting, not re-anchoring.

## Standing note

Do not resolve any ABSENT row by relaxing or deleting the spec. A correctly-failing
spec is a legitimate artifact (`.claude/rules/testing.md`). The fix is the missing
capability.
