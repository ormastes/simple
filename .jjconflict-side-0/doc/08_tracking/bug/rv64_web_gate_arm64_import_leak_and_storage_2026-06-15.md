# RV64 web server gate blocked: arm64 import leak (link) + storage unavailable (runtime)

- **Id:** rv64_web_gate_arm64_import_leak_and_storage_2026-06-15
- **Status:** Open
- **Severity:** P1 (blocks the RV64 HTTP + NVFS storage QEMU gate entirely)
- **Found:** 2026-06-15 (codex web-server target verification)
- **Lane:** `test/03_system/os/simpleos_riscv_network_gate_spec.spl` /
  `sh scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --with-storage`
- **Verdict:** NOT VERIFIED — zero GET-200 evidence, no NVFS evidence.

Both blockers are **pre-existing regressions unrelated to the SSH-crypto work**;
the web target was reused from codex session 019e9a76 as the "next target".

## Blocker 1 — boot.spl riscv64 link fails (arm64 import-graph leak)

`SIMPLE_OS_BUILD_BACKEND=cranelift bin/simple os build --scenario=rv64-base`
resolves the correct lane (`entry=boot.spl`, `output=build/os/simpleos_riscv64.elf`,
`backend=cranelift`) but fails at `ld.lld`:

```
undefined symbol: rt_arm64_mrs_sctlr_el1
undefined symbol: rt_arm64_isb / rt_arm64_dsb / rt_arm64_dmb / rt_arm64_wfi / rt_arm64_wfe
undefined symbol: rt_arm64_tlbi_alle1
  referenced by os__kernel__arch__arm64__cpu__* in mod_13.o
```

`rt_arm64_*` have no riscv64 C backing. Reachability is resolved pre-codegen, so
this breaks LLVM identically (backend-independent).

**Root cause:** import-graph leak introduced by `8d27d4deb3b`
("sec(kernel+aop+doc): default-deny kernel caps, fail-closed sandbox boot, …").
Chain into the riscv64 boot reachable set:

```
src/os/kernel/security/sandbox_boot_apply.spl   (arch-neutral boot code)
  └─ use os.kernel.arch_adapt.arm64_sandbox_paging.{arm64_sandbox_pte_bits_from_lowering}
       └─ use os.kernel.arch.arm64.paging.{...}      ← whole-module import
            └─ use os.kernel.arch.arm64.cpu.{msr_*, mrs_sctlr_el1, dsb, isb, tlbi_*}
                 → rt_arm64_*  (no riscv64 symbol)
```

`sandbox_boot_apply.spl` only needs the **pure** text→`[u64]` policy function
`arm64_sandbox_pte_bits_from_lowering`, but pulls it through `paging.spl`, which
also drives real paging via the arm64 CPU intrinsics.

Note: the undefined set includes `dmb/wfi/wfe`, which `paging.spl` does *not*
import from `cpu` — so either the whole `cpu` object links as one unit, or a
second arm64 module is also reachable from riscv64 boot. Do not assume one
repoint closes it; rebuild and let `ld.lld` enumerate the remainder.

### Fix applied (2026-06-15) — arm64 leak CLOSED

1. New CPU-free module `src/os/kernel/arch/arm64/sandbox_pte_bits.spl` holds the
   pure policy functions `_flags_to_pte_bits`, `arm64_sandbox_permissions_to_vm_flags`,
   `arm64_sandbox_pte_bits_for_permissions`, `arm64_sandbox_pte_bits_from_lowering`
   + the `PTE_*` permission constants they use; imports only
   `os.kernel.types.memory_types`.
2. Repointed `src/os/kernel/arch_adapt/arm64_sandbox_paging.spl` to import from the
   new module. `paging.spl` left untouched (arm64 paging cannot be verified on this
   host) — accept the small duplication; dedupe is a follow-up.

**Result:** riscv64 relink (`build/rv64_relink_after_pte_split.log`) shows **zero
`rt_arm64_*` undefined symbols** — leak closed. The build now surfaces a separate,
broader layer (see below).

## Blocker 1b — broad baremetal-link breakage (definitions not in link set)

After the arm64 leak closed, `ld.lld` reports 6 other undefined symbols in the
`rv64-base` `--entry-closure` link from `boot.spl` — all have definitions
somewhere, but none are in the riscv64 link set. Four distinct root causes:

1. **Hosted-runtime fns called from baremetal:** `rt_bytes_from_raw`,
   `rt_bytes_to_text` — defined in `src/runtime/runtime.c` (HOSTED runtime), called
   by `sandbox_boot_apply.spl::embedded_sandbox_lowering_sdn_from_raw_bounds`. No
   baremetal backing. This is the core `8d27d4deb3b` regression: the fail-closed
   sandbox-boot raw-section reader uses hosted byte/text helpers.
2. **Runtime fns absent from linked minimal runtime:** `rt_string_to_upper`;
   `rt_simple_sandbox_section_start/end` (the latter ARE in
   `src/runtime/startup/baremetal/runtime_minimal.c` + registered in
   `runtime_symbols.rs`, but that object is not in this link).
3. **NVMe C driver object not linked:** `simpleos_nvme_write_sector` (used by
   `c_nvme_adapter.spl` / `vfs_boot_init.spl`). **This is the same wall as Blocker 2
   (`storage unavailable rc=-83`)** — the storage write path has no linked driver.
4. **sshd native-emission gap:** `os__apps__sshd__ssh_session__log_raw_println` is
   DEFINED at `ssh_session.spl:52` and used at `:491` in the same file, yet
   undefined at link — the module's native emission drops the local fn.

Each is a separate fix spanning C runtime (needs seed rebuild + bootstrap
redeploy), driver link config, and sshd codegen — i.e. a broad pre-existing
regression of the `rv64-base` baremetal image, well beyond the arm64 leak.

## Blocker 2 — storage service never becomes ready (runtime, rc=-83)

Running the gate on the (Jun-9) prebuilt ELF (`--allow-prebuilt-artifact`):
QEMU booted SimpleOS RV64 (OpenSBI v1.3, `BOOT OK`), network came up
(`[net-riscv] Network service ready`, `Bootstrap TCP shim bound on 0.0.0.0:8080`),
but the storage probe failed and the gate aborted before the HTTP smoke tests:

```
[storage-riscv] Storage unavailable rc=-83  → [init] storage: unavailable
[fs-riscv] Filesystem unavailable: storage gate not ready
GATE_EXIT=1
```

Serial: `build/qemu-rv64-serial.log` (copy `build/rv64_gate_prebuilt.log`).
Unknown whether `rc=-83` is a stale-prebuilt artifact or a real second
regression — only a clean riscv64 rebuild (blocker 1) can disambiguate.

## Evidence

- `build/rv64_http_storage_gate_findings.md` (full subagent findings)
- `build/rv64_cranelift_build.log` (link failure)
- `build/rv64_gate_prebuilt.log` / `build/qemu-rv64-serial.log` (storage rc=-83)

## Blocker 0 — the gate REQUIRES the LLVM backend, which won't compile (foundational)

`scripts/qemu/qemu_rv64_http_test.shs` (lines 98-100) accepts a from-source build
ONLY if `${ELF}.build_stamp` contains all of:
`backend=llvm`, `target=riscv64-unknown-none`, `entry=src/os/kernel/arch/riscv64/boot.spl`.

So the cranelift `rv64-base` build (what the diagnosis used, and where the arm64
leak was fixed) can **never** satisfy the gate — it stamps `backend=cranelift`.
The gate insists on the LLVM backend compiling the `boot.spl` lane.

But **no `simple` binary has LLVM** (all report "native backend 'llvm' is not
available"), and `cargo build --features llvm` fails (LLVM 18.1.8 present):
undefined `i8_type`/`i32_type`/`context` at
`compiler/src/codegen/llvm/functions/calls.rs:2255-2269`, E0283 at
`functions.rs:2376` (`build/rv64_llvm_cargo.log`). This is a **Rust seed** bug and
the foundational blocker: without an LLVM-capable compiler, the gate fails at the
stamp check regardless of the link/runtime fixes below.

Good news: the gate's required `entry=boot.spl` is the SAME lane the arm64 fix was
made on, and the agent confirmed the arm64 leak "breaks LLVM identically"
(reachability is resolved pre-codegen). So the arm64 fix is on the correct lane and
helps the LLVM build once it compiles.

Note: `simpleos_nvme_write_sector` has **no C definition anywhere in `src/`** (only
`extern fn` declarations in `c_nvme_adapter.spl`, `c_nvme_block_adapter.spl`,
`q35_pure_nvme_perf_boot.spl`, `vfs_boot_init.spl`) — a phantom extern. This is
why storage fails `rc=-83`: there is no NVMe write driver to link.

## Feature requests (non-pure-Simple follow-ups required to green the web gate)

Per scope decision (pure-Simple fixes preferred; C/seed only as fallback, tracked):
these all require Rust-seed or C-runtime/driver work and are filed as requests:

- **FR-1 (Rust seed, foundational):** repair the LLVM backend build —
  `codegen/llvm/functions/calls.rs:2255` undefined `i8_type`/`i32_type`/`context`,
  E0283 at `functions.rs:2376` (inkwell API usage). Needs `cargo build` +
  bootstrap redeploy + post-deploy smoke (the `--deploy` stage4 has no smoke gate).
- **FR-2 (C runtime / boot-path):** `sandbox_boot_apply.spl` calls hosted
  `rt_bytes_from_raw` / `rt_bytes_to_text` (+ `rt_string_to_upper`) that have no
  baremetal backing; either add baremetal-safe primitives or redesign the
  `.simple.sandbox` raw-section reader to avoid hosted runtime on baremetal.
- **FR-3 (C runtime link):** ensure `runtime_minimal.c` (`rt_simple_sandbox_section_*`)
  is in the riscv64 `--entry-closure` link set.
- **FR-4 (driver):** provide a real `simpleos_nvme_write_sector` (and the
  read/init siblings) implementation, or route the riscv64 storage boot to the
  pure-Simple NVMe path; without it NVFS storage cannot come up (`rc=-83`).
- **FR-5 (codegen):** `os__apps__sshd__ssh_session__log_raw_println` is defined and
  used within `ssh_session.spl` yet dropped from native emission — investigate the
  local-fn emission gap for the baremetal closure.
