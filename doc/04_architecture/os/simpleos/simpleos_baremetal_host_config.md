# SimpleOS Baremetal vs Host Configuration

**Status:** Architecture / configuration reference. Code-anchored to the tree at `/home/ormastes/dev/pub/simple` (2026-07-08). Every claim cites `file:line`; where a claim could not be verified in code it is marked **[unverified]** or **[not found]**.

**One-line thesis:** SimpleOS is meant to run in two mutually-incompatible configurations — a **HOST/HOSTED** dev-and-test config and a **BAREMETAL** in-guest config — but the split is *not* carried by one clean switch. It is scattered across (a) which stdlib **tier** you import, (b) **build-time** catalog entries (entry `.spl`, `crt0`, link flags), (c) the **arch** `@cfg` atom + `compiled/interpreter`, (d) a compile-time desugar **strict profile**, (e) **link-time C-vs-Simple** selection of `@export("C")` externs, and (f) **runtime** provider flags (`pure_simple`). The intended `@cfg(baremetal)` predicate is effectively **inert** (see §3.3, §6-L1).

---

## 1. Purpose — why two configs, not one with flags

Host and baremetal are not two settings of one program; they are two different execution substrates whose invariants contradict each other, so code correct in one is silently wrong in the other:

- **The allocator model differs.** The baremetal native-build runs on a freestanding bump allocator whose grow-copy corrupts element bytes; a growable `[u8]` built with `.push()` (fine on host) arrives with mangled data on baremetal (`examples/09_embedded/simple_os/arch/x86_64/fs_exec_general_ring3_entry.spl:44-52`). The noalloc tier forbids heap allocation entirely (`src/lib/nogc_async_mut_noalloc/__init__.spl:30-34`).
- **Static initialization differs.** Module-level `val` initializers **do not run** under freestanding native-build, so a top-level constant reads garbage at runtime and can triple-fault before user code executes (`examples/09_embedded/simple_os/arch/x86_64/ring3_smoke_entry.spl:42-47`; `fs_exec_general_ring3_entry.spl:27-28`).
- **Value representation differs.** Under freestanding native-build a `[u8]` is stored as boxed `RuntimeValues` read stride-1, so byte parsing off `image.file_bytes` yields garbage (`phoff=16`); the loader must instead parse ELF via MMIO off the raw identity-mapped buffer (`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:50-53, 288-295`).
- **The backend surface differs.** Host has an allocator, syscalls, and a window server (Cocoa/SDL2). Baremetal has none of these — only MMIO, interrupts, and semihosting SFFI (`src/lib/nogc_async_mut_noalloc/__init__.spl:34`).

A single binary with runtime flags cannot satisfy both: the hazards above are decided at **compile/build** time, not by a boolean at runtime. Hence two configs.

---

## 2. The two configurations defined

### 2.1 HOST / HOSTED (dev + test)

| Aspect | What it is | Anchor |
|---|---|---|
| Executor | Pure-Simple self-hosted binary / interpreter (`bin/simple test`, `run`) | CLAUDE.md "Default tooling"; `_pp_eval_atom` `interpreter`→false / `compiled`→true `src/compiler/10.frontend/core/parser_preprocessor.spl:26-29` |
| Allocator | Host runtime (`rt_array_new`, `rt_alloc`) — growable `[u8]`/`.push()` safe | contrast note at `fs_exec_general_ring3_entry.spl:44-52` |
| Backends | Hosted stand-ins: Cocoa/SDL2 compositor, in-memory NVFS, loopback socket pair | `src/os/compositor/hosted_backend_cocoa.spl:16`; `src/os/kernel/net/loopback_socket.spl:1-15` |
| Platform lane | `aarch64-apple-darwin` "hosted lane — native Mac process, no QEMU, no bare-metal" | `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl:826` |
| Guarantees | Fast iteration; runs on a dev workstation; extern-free paths are unit-testable | `loopback_socket.spl:5-10` |
| Forbids (should) | Shipping in the booted kernel image — hosted stand-ins are not real hardware paths | audit `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md` §2 desktop-gui/networking rows |

### 2.2 BAREMETAL (in-guest kernel)

| Aspect | What it is | Anchor |
|---|---|---|
| Executor | Freestanding native-build ELF; `-nostdlib -static`, no libc | `platform_target_catalog.spl:182` (x86_64 `link_flags`) |
| Entry / startup | `crt0.s` sets long mode + 64-bit GDT, jumps `spl_start` | `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:1-16` |
| Allocator | Freestanding bump allocator (grow-copy corrupts); noalloc tier = no heap | `fs_exec_general_ring3_entry.spl:44-52`; `nogc_async_mut_noalloc/__init__.spl:30-34` |
| Backends | Real MMIO/DMA NVMe+FAT32, BGA framebuffer, netstack+NIC (intended) | `src/os/services/vfs/vfs_boot_init.spl:270,286,288`; `src/os/kernel/boot/init_services.spl:137-143` |
| Privilege | ring-3 handoff via `iretq` to CPL3; TSS init extern `rt_x86_tss_init` | `x86_64_fs_exec_ring3.spl` handoff; `crt0.s:631-663`; `fs_exec_general_ring3_entry.spl:23` |
| Target | QEMU (`qemu-system-*`) / real hardware / FPGA M-mode | `platform_target_catalog.spl` x86_64 qemu lane; `:591` (riscv64 `BareMetal` FPGA lane) |
| Guarantees (must) | No host syscall/allocator/SDL; freestanding-safe patterns only | §5 below |
| Forbids | Module-level `val` init, growable `.push()`, boxed `[u8]` reads, host allocator | §5 |

---

## 3. Where the config split actually lives

### 3.1 Build-time — stdlib tiers (`src/lib/`)

Tier selection is the coarsest config switch: importing a tier commits to its allocator/GC/async assumptions.

| Tier | GC? | Alloc? | Async? | Host deps? | Anchor |
|---|---|---|---|---|---|
| `common` | pure functions, no runtime assumptions | — | — | none | no `__init__.spl`; `src/lib/common.spl` is a namespace anchor (`val common_namespace_anchor = true` `:6`) |
| `nogc_sync_mut` | `@no_gc` | yes (mimalloc) | no | host allocator/FS/net | `src/lib/nogc_sync_mut/__init__.spl:1` (`@no_gc`), `:20` (`export MimallocAllocator`) |
| `nogc_async_mut` | `@no_gc` | yes | yes (both `async_embedded` + `async_host`) | `async_host` present | `src/lib/nogc_async_mut/__init__.spl:1, 31, 45` |
| `gc_async_mut` | `@gc` | yes | yes | GPU/CUDA/ML | `src/lib/gc_async_mut/__init__.spl:1` |
| `nogc_async_mut_noalloc` | `@no_gc` | **no** (`alloc_allowed:false`) | cooperative only | **none** ("No OS", SFFI = MMIO/interrupts/semihost) | `src/lib/nogc_async_mut_noalloc/__init__.spl:30-34, 36` |

Per CLAUDE.md, `nogc_async_mut_noalloc` is the baremetal tier; its `__init__` states the constraints explicitly (`:30-34`): `@no_gc` forbids GC, `alloc_allowed:false`, no heap, no OS (cooperative scheduling only), SFFI limited to MMIO/interrupts/semihosting. **Note:** these constraints are a **comment block**, not enforced fields — the `:31` line reads `alloc_allowed: false (enforced by BaremetalConfig)`, but `BaremetalConfig` appears **only in that comment** (no struct exists; `grep 'BaremetalConfig' src/lib` returns the single comment line). `nogc_async_mut` is the stdlib default (per memory) and notably carries **both** `async_embedded` and `async_host` variants (`:31, 45`) — i.e. the host-vs-baremetal split is pushed *inside* this tier as separate modules, not a flag.

### 3.2 Build-time — platform target catalog

`src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` (`simpleos_platform_targets()` `:11`) is the authoritative per-target build config. Each `SimpleOsPlatformBuildTarget` carries the baremetal/host distinction as concrete fields:

| Field | Baremetal meaning | Example anchor |
|---|---|---|
| `default_entry` / lane entry `.spl` | Which top-level `.spl` boots — a real boot vs a probe fixture vs a hosted payload | x86_64 `default_entry` `os_entry.spl` `:34`; acceptance lane `fs_exec_entry.spl` `:62` |
| `boot_asm_sources` (`crt0`) | The freestanding startup stub | x86_64 `crt0.s` `:160` |
| `boot_impl_kind` | `StandaloneAsm`/`EmbeddedAsm`/`NativeC` | x86_64 `StandaloneAsm` `:177`; enum `src/os/port/_SimpleosMultiplatformBuild/build_target_contracts.spl:11-15` |
| `runtime_impl_kind` | `Simple` — runtime is pure-Simple, not C | x86_64 `:178` |
| `standalone_asm_policy` | `Disallowed`/`EntryStubsOnly`/`BroadNativeSurface` — how much native surface is allowed | x86_64 `EntryStubsOnly` `:179`; darwin `Disallowed` `:822`; enum `build_target_contracts.spl:18-21` |
| `link_flags` | `-nostdlib -static …` marks freestanding | x86_64 `["-nostdlib", "-static", "-z", "max-page-size=0x1000"]` `:182` |
| `boot_firmware_contract` | `LimineBios`/`OpenSbi`/`RawLoader`/`BareMetal`/**`HostedPayload`** | riscv64 FPGA `BareMetal` `:591`; darwin `HostedPayload` `:766` |
| `default_image_layout` | `Fat32Disk`/`VirtioFat32`/**`HostedVirtioFat32`** | darwin/riscv64 hosted `:767, 515` |
| `SimpleOsLaneKind` | `Smoke`/`FsExec`/`BoardCompileSmoke`/**`HostedCompileSmoke`** | riscv64 hosted `:543`; darwin `:778` |

The darwin entry is the explicit hosted config: `notes:"aarch64-apple-darwin hosted lane — native Mac process, no QEMU, no bare-metal. Goes GREEN on Apple Silicon Mac, RED (missing-media) on Linux by design."` (`:826`); its `standalone_asm_policy: Disallowed` (`:822`) and `HostedPayload` firmware contract (`:766`) confirm it is not freestanding.

### 3.3 Build-time — `@cfg` atoms (and the baremetal gap)

`@cfg`/`@when` conditionals are stripped by the text preprocessor; atom evaluation is `_pp_eval_atom` (`src/compiler/10.frontend/core/parser_preprocessor.spl:14-76`), reached via `_pp_eval_condition` (`:291, 316, 420`):

- `false`→false (`:20-21`), `debug`→true / `release`→false (`:22-25`), `compiled`→true / `interpreter`→false (`:26-29`)
- **arch atoms** `x86_64`/`x86`/`aarch64`/`arm`/`riscv64`/`riscv32`/`ppc64le` → `cfg_detect_arch()` (`:53-65`) — a real, working selector (90× `@cfg(x86_64)`, 81× `@cfg(arm64)` in `src/`)
- OS atoms, then `key==value` → `cfg_eval_key_value`
- **fallthrough → `false`** (`:76`)

**Load-bearing finding:** there is **no `baremetal` case** in `_pp_eval_atom` (`:14-76`). A bareword `@cfg(baremetal)` therefore resolves to **false**, and `@cfg(not(baremetal))` to **true**, in every build that runs this preprocessor — kernel or host alike. This governs **7** `@cfg(baremetal)` and **10** `@cfg(not(baremetal))` sites (e.g. the RDRAND/RNDR entropy stubs `src/os/kernel/net/tls_shim.spl:106,120`; the ARM loader `@export("C")` host stubs `src/os/kernel/loader/segment_mapper.spl:44-88`). Net effect: the `@cfg(not(baremetal))` host stubs are **kept**, the `@cfg(baremetal)` real definitions are **stripped**. The preprocessor itself documents this false-negative-survival risk in a comment (`:194-197`).

The one predicate that *could* express host-vs-baremetal is `os==simpleos`: `cfg_normalize_os` recognizes `"simpleos"`/`"SimpleOS"` (`src/compiler/10.frontend/core/cfg_platform.spl:59-62`) and `cfg_eval_key_value` handles the `os` key (`:203`) and `platform` key (`:212`). But a grep for `os==simpleos` / `platform==simpleos` / `@cfg(...simpleos...)` across `src/os`, `src/lib`, `examples/09_embedded/simple_os` returns **zero hits [not found]**. So the working `os==simpleos` switch exists in the evaluator but is **unused**; and a bareword `@cfg(simpleos)` would also be false (no atom case). **Conclusion: baremetal-vs-host is not carried by any working `@cfg` predicate today** — `@cfg(baremetal)` is aspirational. **[The possibility that a native/compiled build injects `baremetal`=true through a non-frontend path was searched (`src/app/cli/native_build_main.spl`, `src/compiler/80.driver/driver_aot_output.spl`) and not found; flag for confirmation.]**

### 3.4 Build-time — desugar strict "baremetal profile" (Pass A)

A second, distinct compile-time axis lives in the desugar frontend: a **strict baremetal frame-verification profile**. `src/compiler/10.frontend/desugar/frame_verify.spl` implements "Pass A enforcement from the v0.3 baremetal async spec" (`:4`); "In strict mode (baremetal)" (`:6`) limit violations become **errors** rather than warnings (`:128`). `default_baremetal_limits()` (`:39-47`) returns `strict: true`; the non-baremetal profiles return `strict: false` (`:55, 63`). Two sibling passes gate on the same profile: `spawn_analysis.spl:4` and `reservation_analysis.spl:4` are "Required for baremetal strict mode where task pools / `pool.take()` is infallible". The pass is exported from `desugar/__init__.spl:17` (`export default_baremetal_limits`). **[Unverified: the *trigger* — what makes the desugar select `default_baremetal_limits()` / strict mode for a given target — was not located; the strict-profile code exists but its per-target selection wiring is not confirmed.]**

### 3.5 Build-time — link-time C-vs-Simple externs (the de-facto selector for `@export("C")` stubs)

Because `@cfg(baremetal)` is inert (§3.3), the class of `@cfg(not(baremetal)) @export("C")` functions is actually resolved at **link time**, not by `@cfg`: the Simple stub body is compiled for host/interp, while the real implementation is supplied by a C object linked only into the freestanding build. The C files exist per-arch — `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`, and for riscv64 both `src/os/kernel/arch/riscv64/boot/baremetal_stubs.c` and `.../freestanding_runtime.c`. Verified that the arch `baremetal_stubs.c` objects actually define the same externs the Simple side stubs (`rt_arm64_user_as_create`, `rt_arm_stage_raw_image`, `rt_arm64_user_as_map_page` all present in `examples/09_embedded/simple_os/arch/{arm32,arm64,x86_64}/boot/baremetal_stubs.c`; the x86_64 object defines ~134 `rt_*` symbols). The harness `crt0.s` names this directly: the 64-bit TSS descriptor is "filled at runtime by `rt_x86_tss_init` (`baremetal_stubs.c`)" (`examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:656`). So for these externs the real host-vs-baremetal selector is **which object gets linked**, and the kept Simple stub is only the host/interp fallback (see the L1 collision hazard, §6).

### 3.6 Build-time — crt0 variants

| crt0 | Role | Anchor |
|---|---|---|
| Generic backend | Multiboot2 header, stack setup, BSS zero, `call main()`. Minimal; no ring-3/GDT/TSS | `src/compiler/70.backend/baremetal/x86_64/crt0.s:1-18` |
| SimpleOS harness | Multiboot1 header, 32→64 mode switch, identity-map, loads 64-bit GDT (incl. ring-3 + TSS), jumps `spl_start` | `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:1-16` |

The harness crt0 is the one referenced by the catalog (`platform_target_catalog.spl:160`). Two facts corrected against the header text:

- **Identity-map size is 4 GiB, not 2 GiB.** The header *comment* says "first 2 GiB" (`crt0.s:13, 64`), but the actual page-table code maps **4 GiB**: `PDPT[0..3] -> PD[0..3]` "(4 GiB identity map)" (`:67`), "Fill PD[0..2047] … (4 GiB total)" (`:109`) — plus a high PD for OVMF/q35 MMIO near `0xC000000000` (`:69, 122-133`). The 2 GiB comment is stale.
- **The DPL3/TSS ring-3 keystone IS in this crt0.** The 64-bit GDT declares user CS/SS at **DPL=3** (selectors `0x18/0x20/0x28`, access bytes `0xFA`/`0xF2`, `:631-651`) and a 16-byte TSS system-descriptor slot `gdt64_tss_desc` (`:593, 602, 660-661`), with ring-3 `iretq` stubs (`:523, 529`). The TSS descriptor is reserved (present=0) in the image and patched at runtime by `rt_x86_tss_init` (`:656-657`; extern reached at `fs_exec_general_ring3_entry.spl:23`). (Previously hedged as unverified — now directly confirmed in the header.)

### 3.7 Runtime — backend provider flags

The single clearest *runtime* host-vs-baremetal switch is the VFS storage-provider flag:

- `vfs_boot_storage_is_pure_simple()` returns `g_vfs_boot_storage_pure_simple` (`src/os/services/vfs/vfs_boot_init.spl:1587`).
- The pure-Simple NVMe→FAT32 path sets `provider="simple-driver"`, `pure_simple=true` (`vfs_boot_init.spl:321-322`); the VirtIO path sets `provider="virtio-blk"` (`:888`), `pure_simple=true` (`:889`).
- `vfs_boot_storage_acceptance_reason` **rejects** any non-pure-simple provider — `"vfs-boot-storage-not-pure-simple:"+provider` (`vfs_boot_init.spl:1594`), and further requires `provider=="simple-driver"` (`:1596`).
- Callers gate on it: `g_vfs_initialized and not vfs_boot_storage_is_pure_simple()` (`vfs_init.spl:75`, `vfs_write_ops.spl:35`).
- Other provider/mode strings live in the perf lane contract, e.g. `c_bridge_used=false`, `storage_provider=simple-driver`, `network_provider=simple-driver` (`platform_target_catalog.spl:104-130`).

---

## 4. Per-subsystem backend matrix

Status column = does the **booted baremetal image** actually use the baremetal way? Direct code anchors preferred; audit cited for synthesis.

| Subsystem | Host backend | Baremetal backend | Selection mechanism | Status (baremetal uses baremetal way?) |
|---|---|---|---|---|
| **Storage/FS** | In-memory NVFS arena; hosted FAT32; minimal reader | Pure-Simple NVMe→DMA→FAT32; real `alloc_dma` + `mmio_read32`/`write8` | Runtime `pure_simple` flag (`vfs_boot_init.spl:178,321-322,1587`) | **Partial-real.** Boot path *does* use real MMIO/DMA (`:270,286,288`), but only a single-cluster / first-4 KB reader `vfs_boot_read_pure_nvme_fat32_path_bytes` (`:738`); the full `services/fat32` driver (`Fat32Core.new`+`.mount` `:880-881`), NVFS, DBFS are **not** mounted in boot (audit §2 storage-fs) |
| **Networking** | `loopback_socket` in-memory fd pair for 127.0.0.1, extern-free (`loopback_socket.spl:1-15`) | netstack IPC + NIC driver (intended); `socket_compat` routes non-loopback to netstack (`src/os/kernel/socket_compat.spl:18-22, 42-47`) | Address-based dispatch in `socket_compat` (loopback vs `_ensure_netstack_fd`) | **No.** No NIC/x86_64 net path exists (`loopback_socket.spl:16-21` ponytail); `posix_socket()` allocates a local fd without contacting the netstack (`socket_compat.spl:98`, comment `:43`), so the Simple stack is never bound to a NIC (audit §2 networking) |
| **IPC** | `message_buffer` module-global arrays; `InlineChannel`/`L4BufferPool` instance fields | L4-style inline (≤64 B regs) + shared-page zero-copy; "primitive types for baremetal ABI safety" | Compile-time inclusion; runtime port registration | **Partial.** Code present and baremetal-ABI-shaped (`src/os/kernel/ipc/message_buffer.spl:9`), but module-global (not per-process) and untriggered in boot; interpreter can't even exercise module-global arrays (`:11-19`); audit §2 ipc-sync |
| **Display/GUI** | `HostedCocoaBackend` / SDL2 / web panel compositor (`compositor/hosted_backend_cocoa.spl:16`) | BGA framebuffer via I/O ports `0x01CE/0x01CF`, 1024×768×32 (`init_services.spl:137-143`) | Which service init runs; `_init_display_service()` | **Weak.** `_init_display_service` calls `bga_init_framebuffer` (`:141`) but returns `true` unconditionally (`:143`); compositor/WM run only as hosted app, never launched by `os_main` (audit §2 desktop-gui) |
| **Memory/alloc** | Host `rt_array_new`/`rt_alloc`; growable `.push()` safe | Freestanding bump (`fs_exec_general_ring3_entry.spl:44-52`); noalloc allocators (`noalloc/__init__.spl`) | Tier import + native-build | **Yes (where it runs).** Boot uses `rt_bytes_from_raw` pre-sizing and MMIO, avoiding the bump-grow hazard (`vfs_boot_init.spl:632`) |
| **Test** | `bin/simple test` interpreter/host | QEMU lanes: `qemu_smoke_lane`, `qemu_acceptance_lane`, `board_lane` per target | `platform_target_catalog.spl` lane entries | **Split by design.** Interpreter path cannot exercise some baremetal-shaped code (`message_buffer.spl:11-19`) |

---

## 5. "Baremetal Ways" — the discipline the baremetal config MUST follow

Each rule is baremetal-only and tied to the concrete hazard it avoids. All are documented in code comments today:

1. **Constants must be function-local, never module-level `val`.** Hazard: module-level `val` initializers do not run under freestanding native-build → the constant reads garbage → e.g. `RIP` non-canonical → triple fault before user code. Anchor: `ring3_smoke_entry.spl:42-47`; `fs_exec_general_ring3_entry.spl:27-28`.
2. **Build byte buffers with `rt_bytes_from_raw` (pre-sized), never growable `[u8]` + `.push()`.** Hazard: `.push()` starts at cap 16 and grows via realloc-copies; the freestanding bump allocator's grow-copy corrupts element bytes (length survives, data does not). `rt_bytes_from_raw` → `rt_array_new(n)` pre-sizes so no realloc runs. Anchor: `fs_exec_general_ring3_entry.spl:44-52` (same helper used by `vfs_boot_init`).
3. **Parse structured data via MMIO off the raw identity-mapped buffer, not off boxed `[u8]`.** Hazard: freestanding native-build stores `[u8]` as boxed `RuntimeValues` read stride-1, so `byte_utils` reads yield garbage (`phoff=16`); MMIO reads off the raw buffer decode the true on-disk bytes. Anchor: `x86_64_fs_exec_ring3.spl:50-53, 288-295`; the loader re-reads `e_entry` at offset 24 via `_rd64` (`:302-303`).
4. **Do not trust module-`val`-bound structured fields (`image.entry`, `image.initial_sp`, `stack_top`); recompute function-locally.** Hazard: the `elf_loader`/`stack_builder`/`process_image` chains key on module-level `val`s (rule 1) → unreliable freestanding. Anchor: `x86_64_fs_exec_ring3.spl:23-28, 317-320`.
5. **Use real DMA drivers and real MMIO for devices — no host stand-ins.** The boot storage path allocates real DMA (`g_nvme.alloc_dma` `vfs_boot_init.spl:270`), zeroes and reads via `mmio_write8`/`mmio_read32` (`:286, 401`), and submits on a real NVMe queue (`:288`). Note the width-comparison caveat: the u8 PCI-class match `pcimgr_find_by_class` silently mismatches NVMe on baremetal Cranelift, so the i64 variant is required (`vfs_boot_init.spl:166-170`, SYS-GUI-007).
6. **No host syscall/allocator/SDL assumptions.** Baremetal entropy uses gated stubs, not host RNG — and today only an LCG stub (`tls_shim.spl:106-126`, Knuth LCG at `:116`, "NOT cryptographically secure" `:112`, "Replace with real RDRAND/RNDR" `:101`), which is a real production gap, not a baremetal *way* satisfied.
7. **Freestanding link discipline:** `-nostdlib -static` + `crt0` entry-stub-only native surface (`platform_target_catalog.spl:182, 179`); the real bodies of `@export("C")` baremetal externs come from the linked C object (§3.5), not the Simple stub.

---

## 6. Leak / gap list — where baremetal reuses host assumptions or only runs hosted

Cross-linked to `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md` (a **committed** assessment — tracked and clean in git; cited for synthesis).

- **L1 — `@cfg(baremetal)` is inert (the config switch itself leaks).** Bareword `baremetal` has no case in `_pp_eval_atom` (`parser_preprocessor.spl:14-76`) → false everywhere; `os==simpleos` would work but is unused (`cfg_platform.spl:59-62` normalizes `simpleos`; **0 usages [not found]**). Rule violated: "baremetal and host should have DIFFERENT config." Consequence: `@cfg(not(baremetal))` host stubs — e.g. `segment_mapper.spl:44-88` returning `0`/`2` (`:49`, `:70`) and `user_address_space.spl:22` returning `1` — are compiled into *every* build; the real `@cfg(baremetal)` bodies are stripped. The real definitions therefore must arrive via the linked C object (§3.5, `baremetal_stubs.c`), so the safety of these functions rides entirely on link-time selection, not on a working `@cfg` predicate — a stub-vs-real collision risk if the C object is ever missing from a native link.
- **L2 — Networking never uses the baremetal way.** No NIC/x86_64 net path; `posix_socket()` allocates a bare local fd and never binds a NIC (`socket_compat.spl:98`, comment `:43`); the only real wire path is the netstack IPC route, which needs a live `netstack_service` responder that is not wired for x86_64. Anchor: `loopback_socket.spl:16-21`; audit §2 networking. Baremetal silently reuses the host-testable loopback stand-in for the only working path. *(The draft's "`socket()` returns `-38 ENOSYS`" claim is stale — no `-38` literal exists in `socket_compat.spl`; corrected here.)*
- **L3 — Filesystem boot uses a minimal reader, not the real drivers.** FAT32/NVFS/DBFS drivers exist but boot mounts none; live path is a single-cluster/first-4 KB MMIO reader (`vfs_boot_init.spl:738`). Audit §2 storage-fs.
- **L4 — Display is hosted-only; baremetal init is a soft stub.** Compositor/WM run only as Cocoa/SDL2 host apps and are never launched by `os_main`; `_init_display_service` returns `true` regardless of BGA result (`init_services.spl:141-143`). Audit §2 desktop-gui.
- **L5 — IPC is module-global, not per-process, and untriggered.** `message_buffer` state is module-global (`message_buffer.spl:11-19`); the booted image never runs ring-3, so IPC/pipe/signal paths are untriggered libraries. Audit §G1, §2 ipc-sync.
- **L6 — The booted image runs no ring-3 FS-launched process (keystone).** `os_main` reaches only `boot_fs_mount_freestanding_production()` then `start_http_server_baremetal()` / `serial_shell_main(0)` (`src/os/kernel/boot/os_main.spl:21, 31, 43, 50`); the x86_64 QEMU-lane entry is the `fs_exec_entry.spl` probe fixture (`platform_target_catalog.spl:62`). Audit §G1. Every gate/scheduler/syscall path below the keystone is dead in the shipped image.
- **L7 — Entropy is a placeholder on baremetal.** LCG stub, not hardware RNG (`tls_shim.spl:101-126`).

---

## 7. Guidance for adding a new subsystem with correct host AND baremetal configs

1. **Pick the tier deliberately.** Kernel/driver code that must run in-guest imports from `nogc_async_mut_noalloc` (no heap/no OS, `__init__.spl:30-34`) or keeps to `@no_gc` tiers; never pull a `@gc` tier (`gc_async_mut/__init__.spl:1`) into a boot path.
2. **Give the subsystem two explicit backends and one selector.** Follow the storage pattern: a pure/host-testable stand-in (`loopback_socket.spl`, in-memory NVFS) and a real MMIO/DMA baremetal backend, chosen by an explicit flag/provider string (`vfs_boot_storage_is_pure_simple` `vfs_boot_init.spl:1587`) or address dispatch (`socket_compat.spl:42-47`) — not by silent reuse.
3. **Do not rely on `@cfg(baremetal)` for the host/baremetal split until L1 is fixed.** Until `_pp_eval_atom` gains a `baremetal` case (or code adopts `os==simpleos`), express the split via tier import + arch atoms (`@cfg(x86_64)` works, `parser_preprocessor.spl:53-65`) + a catalog entry + a runtime provider flag. If you add a `@cfg(not(baremetal))`+C-body pair, ensure the C object is actually linked into the native build (§3.5) and file a bug referencing L1.
4. **Obey the Baremetal Ways (§5) in any code that can reach native-build:** function-local constants, `rt_bytes_from_raw` pre-sizing, MMIO parse of raw buffers, real DMA, no host allocator/syscall/SDL. Add the same in-code hazard comments so the discipline is discoverable.
5. **Add a build-time target entry and both test lanes.** Register the entry `.spl`, `crt0`/`link_flags`, `boot_impl_kind`, and `standalone_asm_policy` in `platform_target_catalog.spl`, and provide both a host/interpreter test and a QEMU lane so the baremetal path is exercised, not just the hosted stand-in. If the code has frame/reservation constraints, verify the desugar strict profile (§3.4) applies.
6. **Wire it into the booted image, not just the harness.** The recurring failure mode (§6, audit §G1–G6) is "real code, never reached by `os_main`." A subsystem is only baremetal-real once the shipped boot entry calls it under real MMIO/DMA.

---

### Verification notes
- **Fully code-verified:** tiers (§3.1); catalog fields (§3.2); `@cfg` evaluator and the baremetal-inert finding (§3.3); desugar strict profile existence (§3.4); link-time C stub files exist, define the arm/user-AS externs, and `crt0.s:656` names `baremetal_stubs.c` (§3.5); crt0 4-GiB map + DPL3/TSS keystone in-header (§3.6); `pure_simple` runtime switch (§3.7); per-subsystem anchors (§4); Baremetal Ways comments (§5); `@cfg` counts (90/81/7/10) and the `segment_mapper` `0`/`2` + `user_address_space` `1` stub returns (§6-L1).
- **[unverified]:** the per-target *trigger* that selects the desugar strict baremetal profile (§3.4); any non-frontend injection of a `baremetal`=true cfg atom (§3.3).
- **[not found]:** any use of `os==simpleos`/`platform==simpleos`/bareword `@cfg(simpleos)` as a config switch (0 hits across `src/os`, `src/lib`, `examples/09_embedded/simple_os`); a `-38`/`ENOSYS` return in `posix_socket()` (the earlier draft claim was stale — corrected in L2).
