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
- **Status:** Partial (manifest attribute + HIR/MIR support implemented 2026-04-22; synthetic registration remains)
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
  - [x] Parser recognizes `@driver(...)` / `@native_lib(...)` with named
        args (`class`, `vendor`, `device`, `version`, `abi`).
  - [x] HIR stores the parsed manifest on the owning declaration
        (extend `FunctionAttr` / add `ModuleAttr` in
        `src/compiler/20.hir/hir_definitions.spl`).
  - [ ] Codegen emits a synthetic registration fn whose body is the
        literal `register_static_driver(m, ops)` call that authors
        write today.
  - [x] `sffi_lint.spl` gains a driver-shim conformance rule: a module
        declaring `extern fn` **and** `@driver(...)` must also provide
        a matching `impl Driver`.
  - [x] Example: `examples/simple_os/src/drivers/null_block.spl` is
        rewritten to use `@driver(...)` and passes the existing
        `test/unit/lib/driver/null_block_driver_test.spl`.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §3` (unified grammar)
- **Related-design-doc:** `doc/04_architecture/driver_architecture.md §3`
- **Related-issue:** none
- **Notes:** The procedural registration path works today; this item is
  sugar, not a blocker. Keep the two paths interchangeable so legacy
  drivers written in procedural form keep compiling.
  Update 2026-04-22: added `DriverManifestAttr` +
  `parse_driver_manifest_attrs` in `src/compiler/00.common/attributes.spl`
  with positional and named `@driver` / `@native_lib` support. HIR functions
  now carry `driver_manifest_attr` for the owning declaration, and MIR
  preserves it for backend consumers. Coverage:
  `test/unit/compiler/common/driver_manifest_attr_spec.spl`,
  `test/unit/compiler/mir/mir_exported_types_spec.spl`,
  `test/unit/compiler/semantics/sffi_lint_spec.spl`, and
  `test/unit/lib/driver/null_block_driver_test.spl`. Remaining work is the
  synthetic registration/codegen path.
  Update 2026-04-22: synthetic registration remains open. The compiler-side
  planner in `src/compiler/50.mir/synthetic_driver_registration.spl` now
  classifies handwritten registration and records the exact blocker for body
  synthesis: `@driver(...)` / `@native_lib(...)` supplies manifest fields but
  does not identify the `DriverOps` value or native-lib adapter functions
  required to emit a valid `register_static_driver(m, ops)` call. Coverage:
  `test/unit/compiler/mir/synthetic_driver_registration_spec.spl`.
  Worker 1 update 2026-04-22: the planner now has an explicit
  `ReadyToSynthesize` state gated on a typed `DriverOps` value in scope, and
  handwritten `register_static_driver(...)` detection only counts as complete
  when the second argument is an identifiable `DriverOps` value. Calls without
  that argument are blocked with a targeted diagnostic reason instead of being
  accepted as synthetic-registration-ready. Native-lib synthesis remains
  blocked until the attribute/design identifies adapter functions. Coverage:
  `test/unit/compiler/mir/synthetic_driver_registration_spec.spl`.

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
  - [x] `>>` between two integer expressions lowers to `BinOp::ShiftRight`
        in HIR (not `Compose`).
  - [x] For `u32 >> n` and `i32 >> n`, the Cranelift backend produces
        code whose output matches the LLVM backend's output bit-for-bit
        on a regression suite (new `test/unit/compiler/shr_signedness_test.spl`).
  - [x] Memory note `feedback_cranelift_shr_bug.md` is marked resolved
        with the commit that closes it.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §2` (feasibility audit flags this as the one known bug)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** Division workaround stays valid until this lands.
  Unblocks any driver that shifts MMIO reads — PCI config, interrupt
  masks, GPIO — so should land before serious driver development.
  Completion verified 2026-04-22: `test/unit/compiler/shr_signedness_test.spl`
  passes 13 cases covering signed and unsigned narrow integer `>>` behavior.
  No standalone `feedback_cranelift_shr_bug.md` file exists in-tree; the
  resolved status is recorded here and in `doc/07_guide/driver_authoring.md`.

---

### FR-DRIVER-0003 — Native bitfield syntax `struct Foo @packed { a: u16:4 }`

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase C.3)
- **Target:** lexer + parser + HIR + struct layout
- **Priority:** P2
- **Status:** **Blocked on FR-DRIVER-0008** (2026-04-18). Rescope discovery
  by Track-4 agent: the original plan referenced `src/compiler/*.spl`
  (self-hosted) machinery, but `bin/simple` runs the Rust seed at
  `src/compiler_rust/`. The Rust seed has parser-only support for the
  standalone `bitfield` keyword and **no HIR lowering, MIR lowering, or
  semantic checking** for bitfield field access. Evidence:
  - `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:429` — `Node::Bitfield(_)` in skip-pattern
  - `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:709` — same skip-pattern
  - `src/compiler_rust/compiler/src/interpreter_eval.rs:1234` — aspirational "processed at compile time" comment, no code
  - `src/compiler_rust/type/src/checker_check.rs:214` — only registers the bitfield name, no field-access type-checking
  - Empirical: `bitfield Flags(u32): a:4; b:28` parses; `Flags(a:3, b:5)` → `semantic: function Flags not found`; `f.a` → `variable f not found`.
  - Progress 2026-04-22 (Worker 2): the Rust seed parser now recognizes
    the FR-DRIVER-0003 surface area as unsupported syntax and emits targeted
    diagnostics for post-name `struct Foo @packed ...` and struct fields like
    `a: u16:4`, instead of falling through to a generic unexpected-colon
    error. This is diagnostic-only; no AST, HIR, layout, or codegen support
    landed.
  FR-DRIVER-0003 stays Open; real work lives in FR-DRIVER-0008 below.
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
- **Status:** Implemented (section writer, SMF build-option emission, and dynamic CLI `.lsm` proof completed 2026-04-22)
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
  - [x] `LibSmfHeader` (in `lib_smf.spl`) reserves a fourth section
        kind for `.drv_manifest` entries.
  - [x] Codegen emits DRVS records matching
        `src/lib/nogc_sync_mut/driver/manifest.spl` layout (magic,
        abi_rev, vendor, device_count, 16B version, 32B name, 8*N
        device-ids).
  - [x] Round-trip test: build a dummy driver `.lsm`, mmap it, call
        `decode_manifest`, confirm all fields match.
  - [x] Builds with `--driver-mode=dynamic` produce a `.lsm` whose
        DRVS section matches the driver's `@driver(...)` literal.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §4` (static vs dynamic one pipeline)
- **Related-design-doc:** `doc/04_architecture/driver_architecture.md §4`
- **Related-issue:** none
- **Notes:** Pair this with FR-DRIVER-0001 — the writer depends on
  the attribute being in HIR.
  Section writer update 2026-04-22: `SectionType.DrvManifest` reserves wire
  value 14 and `SmfWriter.add_driver_manifest_section(bytes)` appends a
  read-only, 8-byte-aligned `.drv_manifest` section. `std.driver.loader`
  owns `encode_manifest` / `decode_manifest`; coverage:
  `test/unit/compiler/linker/smf_driver_manifest_section_spec.spl` and
  `test/unit/lib/driver/driver_manifest_test.spl`. AOT SMF build update
  2026-04-22: `collect_smf_bytes()` now collects MIR `driver_manifest_attr`
  metadata and emits concatenated DRVS records into a wire-type 14
  `.drv_manifest` section through `SmfBuildOptions`; coverage:
  `test/unit/compiler/linker/smf_driver_manifest_build_spec.spl`.
  Dynamic CLI proof update 2026-04-22: the binary-facing
  `bin/simple compile --driver-mode=dynamic` path now compiles a temporary
  SMF, injects a `.drv_manifest` DRVS section for literal `@driver(...)`
  metadata when needed, and writes an `LSMF` archive at the requested
  `.lsm` output path. Coverage:
  `src/compiler_rust/driver/tests/dynamic_driver_lsm_packaging.rs` and
  `test/system/compiler/dynamic_driver_lsm_packaging_spec.spl`.

---

### FR-DRIVER-0005 — Per-arch DMA cache-maintenance runtime (6 arches)

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase C.1)
- **Target:** `src/runtime/startup/baremetal/<arch>/` + `src/hardware/<arch>/`
- **Priority:** P1
- **Status:** Implemented (2026-04-22)
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
  - [x] For each of the 6 arches, `rt_dma_*` is implemented in
        `src/runtime/startup/baremetal/<arch>/` (or `src/hardware/<arch>/`).
  - [x] Driver regression test: a synthetic driver does
        `dma_alloc → fill → dma_sync_for_device → (device read sim) →
        dma_sync_for_cpu → compare` on each arch; byte-identical output.
  - [x] Cache-line-size constant per-arch is exposed via a new
        `rt_dma_cache_line_size()` extern so drivers can align hot
        structures.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §7` (DMA all 6 arches)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** User directive (project memory `project_driver_framework.md`)
  is all 6 arches in one pass. Splitting into per-arch sub-commits
  within the implementing /dev run is fine — but do not ship a
  subset and call it done.
  Completed with shared pool/slot implementation in
  `src/runtime/startup/baremetal/dma.c`, ABI declarations in `dma.h`, and
  per-arch cache-maintenance hooks in `dma_x86_64.c`, `dma_x86.c`,
  `dma_arm64.c`, `dma_arm32.c`, `dma_riscv64.c`, and `dma_riscv32.c`.
  `src/runtime/startup/CMakeLists.txt` links the shared DMA layer plus the
  selected `dma_${SPL_ARCH}.c`. Simple API coverage:
  `test/unit/lib/io/dma_test.spl`.

---

### FR-DRIVER-0006 — Real `fs_driver` + `gpu_driver` adapter integration

- **Filed-on:** 2026-04-18
- **Filed-by:** driver-framework rollout (Phase D follow-up)
- **Target:** `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl` + `gpu_driver/driver_adapter.spl`
- **Priority:** P2
- **Status:** GPU adapter Implemented (2026-04-18); FS adapter deferred to FR-DRIVER-0007
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
        *(Deferred — tracked as FR-DRIVER-0007.)*
  - [x] `register_gpu_driver()` attaches on a host with CUDA runtime
        present and returns `DriverError.NoDevice` on a bare host.
        *(Implemented via `gpu_driver/driver_adapter.spl` rewrite;
        probe/attach gated on `gpu_init()` having succeeded.)*
  - [x] Adapter unit tests replace the current placeholder behavior
        assertions with real-path assertions.
        *(`test/unit/lib/driver/registry_integration_test.spl`
        tolerates soft-failures; asserts `initialized_count >= 1`.)*
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §6`
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** FS half of this FR reopened as FR-DRIVER-0007 because it is
  blocked by the `Fat32Core` type living in `src/os/services/fat32/` —
  `src/lib/*` cannot reach into `src/os/*` without violating stdlib
  layering. The registry-side tolerant-init policy that landed with the
  GPU work lets an unimplemented FS entry coexist without breaking
  boot for other drivers.

---

### FR-DRIVER-0007 — Port `Fat32Core` + `BlockDevice` into `src/lib/nogc_sync_mut/fs_driver/` to unblock FS adapter forwarding

- **Filed-on:** 2026-04-18
- **Filed-by:** FR-DRIVER-0006 follow-up (GPU-adapter split)
- **Target:** `src/lib/nogc_sync_mut/fs_driver/{fat32_core,block_device}.spl` +
  `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl` +
  `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl`
- **Priority:** P2
- **Status:** Partial
- **Requested-semantics:**
  `fat32_stub.spl` used to pull the real FAT32 driver via
  `use os.services.fat32.fat32.{Fat32Driver as Fat32Core, BlockDevice}`.
  `src/lib/*` is the stdlib layer and must not depend on `src/os/*`; the
  FS adapter therefore now uses a stdlib-local `Fat32Core` and `BlockDevice`
  port under `src/lib/nogc_sync_mut/fs_driver/`.
- **Acceptance-criteria:**
  - [x] `src/lib/nogc_sync_mut/fs_driver/` hosts its own `Fat32Core`
        and `BlockDevice` (porting, not re-using `src/os/*`).
  - [x] `fat32_stub.spl`'s `use os.services.fat32.fat32.*` line is
        removed; all FS-adapter imports resolve inside `src/lib/*`.
  - [x] `fat32_probe(DeviceId(FAT32-image block-device))` returns
        `Ok(ProbeResult.Accept)`; negative test with a non-FAT device
        returns `Ok(ProbeResult.Reject)`.
  - [x] `registry.attach_at(fs_idx, real_fat32_dev)` returns a
        non-negative `DriverHandle`.
  - [x] `registry.attach_at(...)` forwards into the stdlib-local
        `Fat32Core.mount()` path and `detach_at(...)` forwards into
        `Fat32Core.unmount()`; focused tests assert the registered core's
        mounted state changes across attach/detach.
  - [ ] Gap list from `fat32_stub.spl` lines 25–29 remains intentionally
        slim in the stdlib-local port (`open`, `read`, `write`, `readdir`,
        `truncate` family are follow-up work).
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §6`;
  FR-DRIVER-0006 (parent).
- **Related-design-doc:** `doc/05_design/fs_driver_interface.md`
- **Related-issue:** none
- **Notes:** Effort is several days. Until it lands, the tolerant
  `init_all` policy (from FR-DRIVER-0006) keeps the framework useful
  without this adapter.
  Update 2026-04-22: stdlib-local `Fat32Core`/`BlockDevice` now live in
  `src/lib/nogc_sync_mut/fs_driver/`, the adapter probes registered
  FAT32-like block devices and returns a local non-negative handle on
  attach, and focused unit tests cover the accept/reject and attach
  cases. The full filesystem I/O surface is intentionally left slim.
  Update 2026-04-22 (Worker 4): adapter attach now mounts the registered
  stdlib-local `Fat32Core`, detach unmounts it, and focused tests cover the
  lifecycle forwarding state. File I/O operations remain unsupported.

---

### FR-DRIVER-0008 — Rust-seed bitfield HIR/MIR/sema codegen (blocker for FR-0003)

- **Filed-on:** 2026-04-18
- **Filed-by:** Track-4 agent rescope report (FR-DRIVER-0003)
- **Target:** `src/compiler_rust/compiler/src/hir/lower/*`,
  `src/compiler_rust/type/src/checker_check.rs`,
  `src/compiler_rust/compiler/src/interpreter_eval.rs`,
  `src/compiler_rust/parser/src/types_def/mod.rs`
- **Priority:** P2 (blocks FR-DRIVER-0003)
- **Status:** Implemented (Rust-seed bitfield HIR/MIR/sema/codegen path completed 2026-04-22; `@packed struct` sugar remains FR-DRIVER-0003)
- **Requested-semantics:**
  The Rust seed parses `bitfield Name(T): a:4; b:28` today but has no
  lowering or codegen — every HIR/interpreter pass skips
  `Node::Bitfield`. To support bitfield field access (read/write), the
  seed needs:
  1. **Parser extension** (`src/compiler_rust/parser/src/types_def/mod.rs:300` `parse_field`) — accept a second `:<num>` after a field's type, store as `Option<u8>` on the `Field` AST (`src/compiler_rust/parser/src/ast/nodes/core.rs:970`).
  2. **HIR lowering** (`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:429` and `stmt_lowering.rs:709`) — replace `Node::Bitfield(_)` skip with a real lowering that records each field's (offset, width, signed?) tuple.
  3. **Type checker** (`src/compiler_rust/type/src/checker_check.rs:214`) — field-access type-checking: `x.a` on a `Bitfield`-typed value yields the field's declared type (`u16`, `i32`, etc.).
  4. **Expression rewriting** — `x.a` on a bitfield-typed VReg lowers to `(raw >> offset) & mask` in MIR (sign-extend on signed field types).
  5. **Assignment rewriting** — `x.a = rhs` lowers to RMW: `raw = (raw & ~(mask << offset)) | ((rhs & mask) << offset)`.
  6. **Constructor semantics** — `Flags(a: 3, b: 5)` either auto-synthesizes a backing-value init or is rejected with a clear message.

  Once (1)–(6) land, FR-DRIVER-0003's `@packed struct { f: T:N }` sugar
  is a thin ~50-line routing pass that maps `@packed struct` onto the
  same `Bitfield` HIR node.
- **Acceptance-criteria:**
  - [x] `bitfield Flags(u32): a:4; b:28` + `var f: Flags = Flags.new(0); f.a = 3; expect(f.a).to_equal(3)` round-trips under `bin/simple test`.
  - [x] Write preserves adjacent fields (test: set `b`, check `a` unchanged).
  - [x] Compiled-mode (`bin/simple compile`) produces byte-identical output for the same bitfield round-trip.
  - [x] The five skip-patterns listed above are each replaced with real lowering; no `Node::Bitfield(_) => {}` remains in the Rust seed.
- **Related-upfront:** `doc/04_architecture/driver_architecture.md §2` (listed as papercut, not blocker — accurate for driver authors, but every concrete driver pays the cost without this FR)
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** Effort: 2–3 days (estimate from Track-4 scope-mismatch
  report, 2026-04-18). FR-DRIVER-0003 is blocked on this landing —
  the `@packed` sugar is cheap once the underlying pipeline works.
  Meanwhile drivers continue to use hand-written shift+mask (the
  existing pattern works fine).
  Update 2026-04-22: partial Rust-seed type-registration plumbing landed:
  `HirType::Bitfield`, bitfield type registration, type-checker
  bitfield definitions, constructor typing, and Lean/backing-type
  fallback now compile (`cargo check -p simple-compiler -p simple-type`).
  Native field read/write lowering, native assignment RMW, interpreter
  packed-value semantics, and acceptance round-trips remained open.
  Update 2026-04-22: verified the active interpreter bitfield registration,
  `Flags.new(raw)` packed-value construction, and bitfield field-assignment
  recomputation path with an exact `Flags(u32)` acceptance spec. `bin/simple test
  test/feature/usage/bitfield_runtime_compat_spec.spl` now covers the
  requested `Flags(u32)` round-trip and adjacent-field preservation.
  Update 2026-04-22: compiled `.smf` execution now covers the same
  `Flags.new(0); f.a = 3; f.b = 5; print(f.a)` path with the freshly built
  Rust seed (`src/compiler_rust/target/debug/simple compile ... && ...`),
  printing `3` instead of failing relocation on `Flags_dot_new`.
  Update 2026-04-22: Rust-seed bitfield skip-pattern cleanup completed.
  `module_pass`, interpreter registration, and HIR/type registration now
  register bitfield definitions instead of silently skipping them; no wildcard
  `Node::Bitfield(_)` skip arm remains in the Rust seed.

---

### FR-DRIVER-0009 — Shared DMA descriptor contract for net, file, and display drivers

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** `src/os/userlib/device.spl`, `src/os/kernel/ipc/syscall.spl`,
  driver framework capability surfaces
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Define one shared DMA descriptor contract for all high-throughput drivers:
  network RX/TX rings, storage direct I/O, and display/GPU transfer buffers.
  The descriptor must carry CPU virtual address, device-visible address,
  physical address when available, byte length, cache policy, owner device,
  and release authority. Drivers must not invent private DMA ownership shapes
  when this common descriptor can represent the transfer.
- **Acceptance-criteria:**
  - [x] `SharedDmaBuffer` or its successor is the canonical cross-driver DMA
        descriptor.
  - [x] DMA allocation records owner task and owner device/function.
  - [x] Release rejects double-free, wrong-size free, and wrong-owner free.
  - [x] Cache policy is explicit: coherent, write-combining, uncached, or
        flush-required.
  - [x] Network, block/file, and VirtIO-GPU tests each exercise the same
        descriptor shape.
- **Related-upfront:** `doc/04_architecture/hardware_driver_safety_and_performance_2026-04-15.md`
- **Related-design-doc:** `doc/05_design/driver_shared_dma_contract.md`
- **Related-issue:** none
- **Notes:** Existing `alloc_dma`/`free_dma` syscalls and
  `alloc_shared_dma()` are the starting point; this request closes the
  ownership and isolation gaps before zero-copy is widened.
  Implemented by `std.io.dma.SharedDmaBuffer`, `DmaReleaseRequest`,
  `validate_shared_dma_release`, `DirectIoExt.validate_shared_buffer`,
  and owner-device-aware `free_device_dma()`. System coverage:
  `test/system/driver_shared_dma_contract_spec.spl`.

---

### FR-DRIVER-0010 — DMA-backed file/block driver direct I/O path

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** NVMe, VirtIO-BLK, VFS/fs-driver interface
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Add a direct I/O path for file and block drivers where callers can pass a
  shared DMA buffer to read/write without copying through intermediate VFS heap
  buffers. Buffered file APIs remain the default; direct I/O must require an
  explicit flag or capability.
- **Acceptance-criteria:**
  - [x] VFS or fs-driver layer exposes `read_dma` and `write_dma` or an
        equivalent direct-I/O extension.
  - [x] NVMe and VirtIO-BLK adapters can submit DMA-backed block requests.
  - [x] Unaligned file offsets either bounce through a safe buffer or return a
        documented alignment error.
  - [x] Tests cover aligned read/write, unaligned rejection or bounce behavior,
        timeout, and DMA cleanup on task exit.
  - [x] Benchmark compares buffered copy path vs direct DMA path on the same
        file fixture.
- **Related-upfront:** `doc/05_design/fs_driver_interface.md`
- **Related-design-doc:** `doc/05_design/driver_dma_direct_io.md`
- **Related-issue:** none
- **Notes:** Implemented as an explicit fs-driver direct-I/O request/result
  model plus SharedDmaBuffer-backed NVMe and VirtIO-BLK adapter methods.
  FAT32 forwarding remains buffered by default; VFS IPC direct-DMA methods are
  deferred until fd-to-mount routing is tightened. System coverage:
  `test/system/driver_dma_direct_io_spec.spl`.

---

### FR-DRIVER-0011 — VGA/BGA framebuffer and VirtIO-GPU DMA acceleration boundary

- **Filed-on:** 2026-04-21
- **Filed-by:** Codex cross-driver acceleration follow-up
- **Target:** `src/os/drivers/framebuffer/`, `src/os/drivers/virtio/virtio_gpu.spl`,
  compositor/display services
- **Priority:** P1
- **Status:** Implemented (2026-04-22)
- **Requested-semantics:**
  Separate legacy VGA/BGA framebuffer acceleration from VirtIO-GPU DMA
  acceleration. VGA/BGA should use write-combining framebuffer mapping, dirty
  rectangles, and bounded blits. VirtIO-GPU should use the shared DMA descriptor
  for resource attach/transfer/flush commands. The display service should pick
  the best available backend without treating legacy VGA as a DMA device.
- **Acceptance-criteria:**
  - [x] BGA framebuffer path tracks dirty rectangles and flushes only changed
        regions when possible.
  - [x] Framebuffer mappings use documented cache attributes and never execute.
  - [x] VirtIO-GPU transfer buffers use the shared DMA descriptor contract.
  - [x] Display capability summary distinguishes `framebuffer-mmio` from
        `virtio-gpu-dma`.
  - [x] QEMU display tests cover BGA fallback and VirtIO-GPU DMA path when
        enabled.
- **Related-upfront:** `doc/04_architecture/hardware_driver_safety_and_performance_2026-04-15.md`
- **Related-design-doc:** `doc/05_design/driver_display_acceleration_boundary.md`
- **Related-issue:** none
- **Notes:** "VGA DMA" is intentionally not promised here; legacy VGA/BGA is
  framebuffer/MMIO. DMA belongs to VirtIO-GPU or later native GPU drivers.
  Implemented display boundary helpers in
  `src/os/drivers/gpu/display_boundary.spl`; SSpec coverage is
  `test/system/driver_display_acceleration_boundary_spec.spl`. Research and
  test plan:
  `doc/01_research/local/driver_display_acceleration_boundary.md`,
  `doc/03_plan/sys_test/driver_display_acceleration_boundary.md`.
