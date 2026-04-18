# Driver-Framework Feature Requests

Tracker for requests filed against the `std.driver` framework and its
companion compiler/runtime surfaces (SMF loader, per-arch DMA impls,
grammar extensions). The upfront design lives in
`doc/04_architecture/driver_architecture.md` — items in this tracker
extend that design with work that did not fit Phases A–E of the initial
rollout (landed locally 2026-04-18; see memory
`project_driver_framework.md`).

Id scheme: `FR-DRIVER-####`, monotonic, no reuse.
Lifecycle: `Open` → `Accepted` → `Implemented` (link commit/design-doc)
or `Rejected` (one-line reason).

---

## Open Requests

### FR-DRIVER-0001 — Compiler sugar for `@driver(...)` and `@native_lib(...)` attributes

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase B)
- **Target:** driver / compiler frontend + HIR lowering
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Today every driver registers into the shared registry by calling
  `register_static_driver(manifest, ops)` from a hand-written
  registration fn. The design doc promises the one-liner syntax
  `@driver(class = DriverClass.Block, vendor = 0x8086, device = [0x2922, 0x2829], version = "1.0")`
  placed on a `module` or `impl` block, plus
  `@native_lib(abi = "simple", version = "1.0")` for libs. The compiler
  should lower either attribute to an auto-generated
  `register_static_driver(...)` call (plus an emitted `.drv_manifest`
  SMF section entry; see FR-DRIVER-0004).
- **Acceptance-criteria:**
  - [ ] Parser recognizes `@driver(...)` / `@native_lib(...)` with named
        args (`class`, `vendor`, `device`, `version`, `abi`).
  - [ ] HIR stores the parsed manifest on the owning declaration
        (extend `FunctionAttr` / add `ModuleAttr` in
        `src/compiler/20.hir/hir_definitions.spl`).
  - [ ] Codegen emits a synthetic registration fn whose body is the
        literal `register_static_driver(m, ops)` call that authors
        write today.
  - [ ] `sffi_lint.spl` gains a driver-shim conformance rule: a module
        declaring `extern fn` **and** `@driver(...)` must also provide
        a matching `impl Driver`.
  - [ ] Example: `examples/simple_os/src/drivers/null_block.spl` is
        rewritten to use `@driver(...)` and passes the existing
        `test/unit/lib/driver/null_block_driver_test.spl`.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §3` (unified grammar)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** The procedural registration path works today; this item is
  sugar, not a blocker. Keep the two paths interchangeable so legacy
  drivers written in procedural form keep compiling.

---

### FR-DRIVER-0002 — Cranelift `>>` backend fix (disambiguation + signedness)

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase C.2)
- **Target:** `src/compiler_rust/compiler/src/codegen/instr/core.rs` + HIR
- **Priority:** P1
- **Status:** Implemented (FR-0002a VReg-TypeId infra + FR-0002b consumer landed together 2026-04-18)
- **Requested-semantics:**
  The `>>` operator is broken in the Rust bootstrap Cranelift backend
  (memory note `feedback_cranelift_shr_bug.md`). Root cause is two-part:
  1. The HIR `BinOp` enum overloads `>>` as both `ShiftRight` and
     `Compose` (function composition — `src/compiler_rust/compiler/src/hir/types/expressions.rs:405`).
     The parser must disambiguate by context (integer operands →
     `ShiftRight`, lambda/fn operands → `Compose`).
  2. `compile_binop`
     (`src/compiler_rust/compiler/src/codegen/instr/core.rs:152`) calls
     `ensure_i64` which `uextend`s an `i32` operand to `i64` with
     zeroed top bits, then emits `sshr`. For an i32 whose MSB=1 this
     loses the sign — the value becomes a large positive i64 and
     `sshr` no longer matches the original `>>` semantics.
  Fix: flow operand-signedness info from the HIR `TypeId` to
  `compile_binop`; emit `sshr` for signed ints, `ushr` for unsigned;
  use `sextend` / `uextend` accordingly.
- **Acceptance-criteria:**
  - [ ] `>>` between two integer expressions lowers to `BinOp::ShiftRight`
        in HIR (not `Compose`).
  - [ ] For `u32 >> n` and `i32 >> n`, the Cranelift backend produces
        code whose output matches the LLVM backend's output bit-for-bit
        on a regression suite (new `test/unit/compiler/shr_signedness_test.spl`).
  - [ ] Memory note `feedback_cranelift_shr_bug.md` is marked resolved
        with the commit that closes it.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §2` (feasibility audit flags this as the one known bug)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** Division workaround stays valid until this lands.
  Unblocks any driver that shifts MMIO reads — PCI config, interrupt
  masks, GPIO — so should land before serious driver development.

---

### FR-DRIVER-0003 — Native bitfield syntax `struct Foo @packed { a: u16:4 }`

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase C.3)
- **Target:** lexer + parser + HIR + struct layout
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  Drivers and FFI shims frequently need packed bit-level layouts —
  PCI config space, descriptor rings, network headers. Today authors
  write manual shift+mask helpers using existing `HirBinOp::{Shl,
  Shr, BitAnd, BitOr}`. The sugar should accept
  `struct PciConfig @packed { vendor: u16, device: u16, command: u16:16, status: u16:8 }`
  and lower per-field access to the equivalent shift+mask sequence.
  Field writes must read-modify-write the enclosing word; reads must
  zero-extend (unsigned) or sign-extend (signed) per field type.
- **Acceptance-criteria:**
  - [ ] Lexer accepts `<ty>:<bits>` in struct field declarations.
  - [ ] Parser rejects mixing `@packed` with non-bitfield nested
        structs (use an explicit nested struct instead).
  - [ ] HIR lowering emits correct shift+mask for reads and
        read-modify-write for writes.
  - [ ] Round-trip test: `let x: Foo; x.a = 5; assert(x.a == 5)` with
        `a: u16:4` passes.
  - [ ] Example: `examples/simple_os/src/drivers/null_block.spl`
        grows a `@packed` status-register field and still passes its
        unit test.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §2 table` (listed as papercut, not blocker)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** Lower priority because the shift+mask workaround is
  clean in Simple today. Useful once real drivers start touching PCI
  config or virtio descriptors at scale.

---

### FR-DRIVER-0004 — `.drv_manifest` SMF section + emission from `@driver` attribute

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase B follow-up)
- **Target:** `src/compiler/70.backend/linker/lib_smf.spl` + codegen
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  The runtime decoder already exists
  (`src/lib/nogc_sync_mut/driver/loader.spl::decode_manifest` reads the
  "DRVS" magic + 64B header defined in `driver/manifest.spl`). The
  writer is missing: the compiler must emit an SMF section kind
  `.drv_manifest` populated from each module's `@driver(...)` /
  `@native_lib(...)` attribute (depends on FR-DRIVER-0001). Dynamic-
  mode drivers shipped as `.lsm` will then be discoverable via
  section scan, and `99.loader/module_loader.spl` can invoke
  `register_loaded(reg, manifest, ops)` at load time without authors
  writing any runtime registration code.
- **Acceptance-criteria:**
  - [ ] `LibSmfHeader` (in `lib_smf.spl`) reserves a fourth section
        kind for `.drv_manifest` entries.
  - [ ] Codegen emits DRVS records matching
        `src/lib/nogc_sync_mut/driver/manifest.spl` layout (magic,
        abi_rev, vendor, device_count, 16B version, 32B name, 8*N
        device-ids).
  - [ ] Round-trip test: build a dummy driver `.lsm`, mmap it, call
        `decode_manifest`, confirm all fields match.
  - [ ] Builds with `--driver-mode=dynamic` produce a `.lsm` whose
        DRVS section matches the driver's `@driver(...)` literal.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §4` (static vs dynamic one pipeline)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** Pair this with FR-DRIVER-0001 — the writer depends on
  the attribute being in HIR.

---

### FR-DRIVER-0005 — Per-arch DMA cache-maintenance runtime (6 arches)

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase C.1)
- **Target:** `src/runtime/startup/baremetal/<arch>/` + `src/hardware/<arch>/`
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  `src/lib/nogc_sync_mut/io/dma.spl` landed with arch-agnostic API
  and barrier-only interpreter fallbacks. Each supported arch needs
  a real runtime implementation of `rt_dma_alloc`, `rt_dma_free`,
  `rt_dma_virt_of`, `rt_dma_phys_of`, `rt_dma_sync_for_device`,
  `rt_dma_sync_for_cpu`. Required per arch:
  - **x86_64 / x86:** coherent — barriers suffice; back `rt_dma_alloc`
    with a page-aligned allocator that reports `phys = virt`.
  - **aarch64:** `DC CVAC` for clean, `DC IVAC` for invalidate, `DC
    CIVAC` for clean+invalidate; page-aligned coherent-pool allocator.
  - **arm32:** ARMv7 equivalents (`MCR p15, 0, <rd>, c7, c10, 1` etc).
  - **riscv64 / riscv32:** `fence rw,rw` plus CMO extension (`cbo.clean`,
    `cbo.inval`, `cbo.flush`) when available; software fallback otherwise.
- **Acceptance-criteria:**
  - [ ] For each of the 6 arches, `rt_dma_*` is implemented in
        `src/runtime/startup/baremetal/<arch>/` (or `src/hardware/<arch>/`).
  - [ ] Driver regression test: a synthetic driver does
        `dma_alloc → fill → dma_sync_for_device → (device read sim) →
        dma_sync_for_cpu → compare` on each arch; byte-identical output.
  - [ ] Cache-line-size constant per-arch is exposed via a new
        `rt_dma_cache_line_size()` extern so drivers can align hot
        structures.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §7` (DMA all 6 arches)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** User directive (project memory `project_driver_framework.md`)
  is all 6 arches in one pass. Splitting into per-arch sub-commits
  within the implementing /dev run is fine — but do not ship a
  subset and call it done.

---

### FR-DRIVER-0006 — Real `fs_driver` + `gpu_driver` adapter integration

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase D follow-up)
- **Target:** `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl` + `gpu_driver/driver_adapter.spl`
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  The Phase D adapters register the drivers but stub every op
  (`init → Ok(())`, `probe → Reject`, everything else either
  `Ok(())` or `NotSupported`). Replace these stubs with real
  forwarding:
  - `fs_driver`: `init` calls `Fat32Driver.mount` (or equivalent),
    `probe` inspects the block device for a FAT boot sector,
    `attach` returns a handle tied to a `MountId`, `ioctl` maps to
    the FsDriver capability surface.
  - `gpu_driver`: `init` calls `gpu_init()`, `probe` matches on
    known vendor/device ids (NVIDIA, AMD, Intel), `ioctl` maps to
    the gpu module's command surface.
- **Acceptance-criteria:**
  - [ ] `register_fat32_driver()` followed by `registry.probe_at(idx, ...)`
        with a real FAT32-image DeviceId returns `ProbeResult.Accept`.
  - [ ] `register_gpu_driver()` attaches on a host with CUDA runtime
        present and returns `DriverError.NoDevice` on a bare host.
  - [ ] Adapter unit tests replace the current placeholder behavior
        assertions with real-path assertions.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §6`
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** Blocked only by developer time — the framework is ready.
