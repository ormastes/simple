# x86_64 matrix real filesystem execution is not integrated

The x86_64 repository already contains a real CPL3 execution mechanism:

- `x86_64_fs_exec_spawn` stream-opens the selected FAT32 path;
- `x86_64_fs_exec_enter_stream_ring3` validates and maps ELF64 `PT_LOAD`
  segments into a fresh user address space;
- `arch_x86_64_enter_user_task` reaches CPL3 through `iretq`;
- syscall 60 emits bytes through the real LSTAR dispatcher; and
- syscall 0 returns to the saved kernel continuation through
  `rt_x86_ring3_resume` and exposes `rt_x86_ring3_exit_rc`.

That owner is not used by the current SOSIX/QEMU matrix entry. The admitted
x86_64 descriptor builds
`examples/09_embedded/simple_os/arch/x86_64/fs_exec_entry.spl`, whose launch
checks call `rt_x86_64_smf_cli_load` and print fixed PID/launch markers. It
never calls `x86_64_fs_exec_spawn` or either ring-3 handoff. Moreover,
`scripts/os/make_os_disk.shs` only creates the nonce-bound `/FSEXEC.ELF`
payload by default for ARM32, ARM64, RV32, and RV64; x86_64 receives no
equivalent default payload.

The existing x86_64 ring-3 owner is also explicitly a bare-exec path, not a
scheduler task. `baremetal_stubs.c` documents that the process is not a
`Task`, and `x86_64_fs_exec_ring3.spl` documents that its address-space frames
are abandoned after the saved-frame return. `x86_64_fs_exec_spawn_as` returns
the prepared PID after a nonnegative handoff result, but it does not publish
the target exit status or reap that exact process generation. Consequently a
small entrypoint-only edit could prove real CPL3 stdout and exit, but could not
satisfy the frozen filesystem-program contract's scheduler-owned exit/reap
requirement.

## Resume contract

1. Add x86_64 support to the shared nonce-bound payload builder and ELF gate;
   stage the exact payload as `/FSEXEC.ELF` in the x86_64 fs-exec profile.
2. Split the existing ring-3 handoff result into an explicit value containing
   `started`, target exit kind/code, and saved-frame-return status. Do not
   translate a target exit code into a fabricated PID.
3. Register a real scheduler/process-table child generation before handoff,
   bind syscall dispatch to that generation, transition it to exited on
   syscall 0, then wait/reap the same generation after kernel resume.
4. Change the matrix entry to execute `/FSEXEC.ELF` after the real mount/list
   checks and emit `[fs-program] END ... rc=37` only after stdout, exit, and
   reap agree.
5. Add focused sabotage coverage for wrong mounted bytes, CPL0 invocation,
   forged/stale generation, wrong stdout, wrong exit code, missing resume, and
   missing reap before attempting a fresh media rebuild or QEMU run.

Until these steps land, x86_64 boot, nonce, mount, and listing evidence remains
diagnostic; it is not filesystem-program execution evidence.

## Bounded implementation audit (2026-08-12)

The scheduler side is reusable, but it cannot safely authenticate the existing
x86_64 handoff:

- `fs_exec_prepare_spawn_from_bytes` already creates a real bootstrap
  `TaskControlBlock` with a monotonic `TaskId`, parent 0, a private address
  space, mapped image, and ready-queue membership.
- `Scheduler.exit_task_by_id` can transition that exact task to `Zombie` with
  its target status.
- `Scheduler.wait_for_collect` verifies the parent/child relationship, removes
  the exact task, and calls `destroy_user_address_space` during reap. On
  x86_64 that walker frees user page tables and their PML4.

However, `rt_x86_enter_user_first` records only one global
`_ring3_resume_buf`, `_ring3_resume_valid`, and exit-code scalar. It records no
`TaskId`, task generation, address-space id, or expected CR3. The bare syscall
dispatcher accepts syscall 0 whenever that global savepoint is live and
longjmps to it without proving which task/CR3 issued the call. Syscall 60 has
the same bare-exec ambient mode rather than a task-bound stdout sink. The
scheduler's `TaskId` is a monotonic scalar, not a `(slot,generation)` handle,
so there is no generation token available for the assembly/syscall boundary to
validate.

Wrapping this global result with `exit_task_by_id` and `wait_for_collect`, as
the current ARM bootstrap does, would clean memory after a normal return but
would manufacture authentication after the fact. It would not prove that the
observed exit/stdout belonged to that child. No code integration was made.

The minimum safe implementation must first add an x86_64 execution token owned
by the scheduler: `(TaskId, generation, address_space_id, expected_cr3)`. The
entry assembly installs it atomically with the saved frame; syscall dispatch
must compare the active CR3 and token before accepting stdout or exit; resume
must consume the same token once. Only then may the returning coordinator call
`exit_task_by_id`, verify the token and exit status, and `wait_for_collect` the
same child. Tests must sabotage every token field, replay a consumed token, and
attempt exit from a second CR3.

## Implemented static slice (2026-08-12)

The minimum token/lifecycle slice is now implemented. The validated TCB binds
`TaskId`, a non-reused generation (address-space id, or monotonic TaskId for
the hosted sentinel), and expected CR3 into a single-use native token. In the
scheduler-owned profile, syscall 60 and syscall 0 fail closed unless the live
CR3 matches. Exit moves the exact identity and status into a single-use result;
the Simple entry bridge takes that result with the same tuple, marks only that
child zombie, checks its collected status, and reaps it through the scheduler's
x86_64 address-space cleanup.

The shared payload builder/gate now supports x86_64, the fs-exec image profile
stages it by default, and the canonical x86_64 entry invokes the
scheduler-owned launcher after mount/list validation. Legacy non-scheduler
bare-exec profiles retain their prior behavior; token enforcement activates
only when the validated scheduler entry installs it.

Focused evidence passed: 3/3 validation examples, 3/3 token/source sabotage
examples, x86_64 payload ELF gate, C syntax validation, and diff whitespace.
This remains static evidence. No media rebuild or QEMU run was performed, so
the matrix row remains blocked pending the capped live lane.

## First bounded live rebuild attempt (2026-08-12)

The admitted Stage 2 compiler was revalidated at
`2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`.
The rebuild-wrapper self-test, x86_64 kernel-ELF self-test, generic kernel-ELF
self-test, freshly generated x86_64 child payload build, and child payload ELF
gate all passed. Those static artifacts and logs are retained under:

`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/x86_64-real-exec-20260812T-live/static`

The one authorized canonical rebuild was then run with one job and the frozen
compiler/hash:

```text
SIMPLE_BIG_STORAGE=/mnt/data/.simple \
SIMPLEOS_REBUILD_COMPILER=/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple \
SIMPLEOS_REBUILD_COMPILER_SHA256=2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950 \
SOSIX_QEMU_REBUILD_JOBS=1 \
SOSIX_QEMU_REBUILD_RUN_ID=x86_64-real-exec-20260812T-live \
SOSIX_QEMU_REBUILD_TIMEOUT_SECONDS=900 \
sh scripts/check/rebuild-sosix-qemu-media.shs --run --rows x86_64
```

It failed at the link boundary before media construction. The admitted build
reported 152 unexpected freestanding symbols. Representative blockers are
`rt_byte_array_new`, `rt_typed_bytes_u8_push`, `rt_value_int`,
`rt_value_as_u64`, `rt_struct_receiver_valid`, `rt_bytes_from_raw`,
`_get_kernel_start`, `_get_kernel_end`, `spl_x86_on_user_fault`,
`vmm_create_user_address_space`, and `vmm_destroy_user_address_space`. The last
two also carry compiler attribution showing unresolved identifiers in
`src/os/kernel/memory/user_address_space.spl` rather than declared imports.

The complete retained linker transcript is:

`/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-20260812T-live/x86_64/kernel-build.log`

No image was created and no QEMU process was launched. This is diagnostic RED,
not a matrix or release PASS. Resume by fixing the smallest freestanding owner
closure/runtime boundary and the two unresolved VMM identifiers, then use a
fresh bounded rebuild session; do not retry this unchanged command.

## Static link-closure audit and owner repair (2026-08-12)

The retained linker failure has three distinct root groups:

1. **Source resolution:** `user_address_space.spl` imported private functions
   through the aggregate `memory.vmm` facade. The canonical functions in
   `vmm_address_space.spl` are now public, and the architecture-neutral adapter
   imports that owner directly. This removes the two identifiers which HIR had
   explicitly lowered as unresolved globals.
2. **Provider profile mismatch:** the rebuild wrapper used
   `SIMPLE_BOOT_MINIMAL=1` for x86_64. That profile intentionally compiles only
   `baremetal_stubs.c` and excludes `rt_extras.c`, although the new
   scheduler-owned closure reaches typed arrays, boxed values, text conversion,
   volatile access, and raw-byte conversion implemented there. x86_64 now has
   its own full-provider build branch, retains `SIMPLE_NO_STUB_FALLBACK=1`, and
   does not set the minimal profile. The rebuild wrapper self-test and `sh -n`
   both pass.
3. **Expected closure expansion:** the former probe did not reach the real
   scheduler, address-space manager, ELF loader, or interrupt exit path. Their
   collection/allocation/runtime dependencies are therefore honest reachability,
   not modules to strip merely to make the link green.

A post-fix static provider inventory still finds six required ABI functions
with no real definition in the x86_64 boot-provider tree:

```text
rt_value_unbox_int
rt_value_as_u64
rt_value_u64
rt_struct_alloc
rt_struct_receiver_valid
rt_unwrap_or_trap
```

Canonical implementations exist under `src/runtime`, but copying reduced local
shims would be dishonest: the contracts include lossless wide unsigned values,
total tag-aware integer unboxing, registered struct-allocation bounds, and
None/Err trapping. The checked-in `build/os/sysroot/lib/libsimple_runtime.a`
contains the first three value functions but lacks the struct pair and unwrap
function, so that archive is not yet a complete provider either.

No second native build and no QEMU boot were attempted. The admitted Stage 2
binary also has no `check` command (`error: unknown command 'check'`), so it was
not misreported as source-check evidence. Resume at the runtime owner: produce
one target-correct freestanding provider containing all six canonical
semantics, add a symbol/ABI self-check, then allow a fresh bounded kernel build.
Do not add weak/fabricated stubs or relax `SIMPLE_NO_STUB_FALLBACK`.

## Canonical freestanding value registry v1 (2026-08-12)

The compiler ABI audit confirmed that generated code calls the six runtime
symbols but does not dereference their private wide-box or registry layouts, so
the x86_64 repair does not require a compiler ABI migration. A shared,
architecture-neutral freestanding owner now lives at:

- `examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry.h`
- `examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h`

It freezes a 16-byte version-1 wide unsigned box, validates boxes only after
registry membership, maintains bounded fail-closed registries for wide values,
struct allocations, and enums, and protects registry reads/writes with a
freestanding atomic spinlock. Struct receivers must fall within the exact
registered allocation; merely falling anywhere inside the boot heap is not
accepted. Enum unwrap checks registered ownership and exact Option/Result
discriminants before returning a payload or invoking the target panic hook.

The x86_64 adapter provides strong definitions for exactly
`rt_value_unbox_int`, `rt_value_as_u64`, `rt_value_u64`, `rt_struct_alloc`,
`rt_struct_receiver_valid`, and `rt_unwrap_or_trap`. Its existing
`rt_enum_new` registers the allocation before exposing the tagged pointer.
Allocator and non-returning panic behavior remain target-owned hooks, so ARM
and RISC-V can reuse the same semantic owner without dereferencing hosted heap
objects. Their existing providers were not silently replaced in this slice.

Focused evidence command:

```text
sh scripts/check/check-freestanding-value-registry-v1.shs
```

It passes a hosted behavioral/sabotage self-check (lossless `UINT64_MAX`,
negative and boolean unboxing, forged unregistered box, exact struct bounds,
foreign pointer, registered/forged enum, and None trap) and cross-compiles the
real x86_64 freestanding adapter, requiring one strong symbol for each of the
six functions. The x86_64 `baremetal_stubs.c` translation unit also passed
target syntax validation after the enum-registration hook. No kernel rebuild
or QEMU run was performed.

## Fresh bounded verification after registry integration (2026-08-12)

The frozen Stage 2 compiler hash again matched
`2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`.
The registry behavioral/strong-symbol gate, rebuild-wrapper self-test, both
kernel-ELF self-tests, fresh child build, and child ELF gate passed. Static
evidence is retained at:

`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/x86_64-real-exec-registry-20260812/static`

The one authorized strict rebuild then compiled 298 modules and linked the
real scheduler-owned x86_64 kernel successfully as a 479 KiB freestanding ELF:

`build/os/simpleos_x86_64_fs_exec.elf`

This proves the former six-symbol registry/runtime blocker is cleared at the
kernel link boundary. Media construction stopped at its fail-closed capacity
check before producing a run image:

```text
fat_capacity status=fail payload=structural bytes=17772300
required_clusters=17356 allocated_clusters=119797
capacity_clusters=130546 cluster_bytes=1024 minimum_image_mb=135
disk image too small for payload set
```

The canonical rebuild wrapper currently passes a fixed 128 MiB size to
`make_os_disk.shs`; the measured payload set requires at least 135 MiB. Complete
logs are retained at:

- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-registry-20260812/x86_64/kernel-build.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-registry-20260812/x86_64/image-build.log`

No retry and no QEMU boot were performed. Resume by making the per-row image
capacity an explicit checked rebuild contract (not an ad hoc override), then
start a fresh bounded media/QEMU session. This remains diagnostic RED.

## Deterministic media sizing contract (2026-08-12)

The rebuild orchestrator no longer passes a hardcoded 128 MiB size for every
row. `row_minimum_image_mb` records the measured per-profile construction
minimum (x86_64 real-fs-exec is 135 MiB), and the selected size is:

```text
measured minimum + SOSIX_QEMU_IMAGE_HEADROOM_MB (default 16 MiB)
```

Headroom is restricted to `0..128` MiB and the selected image has a closed
hard ceiling of 512 MiB. A selection below the row minimum or above the ceiling
fails before construction. The plan and immutable construction receipt expose
`image_minimum_mb`, `image_headroom_mb`, `image_selected_mb`, and
`image_hard_max_mb`; x86_64 currently selects 151 MiB. The existing explicit
`compiler_in_filesystem` row profile continues to be passed to the media
builder, and construction still copies kernel/image artifacts into a new run
directory rather than mutating an admitted base artifact.

The wrapper self-test passed and includes the measured 135 MiB witness, rejects
the 134 MiB sabotage, rejects headroom above 128 MiB, and compares two generated
sizing receipts for byte-stable output. Shell syntax, plan output, and diff
whitespace checks also passed. No kernel build, media build, or QEMU boot was
performed for this sizing-only change.

## Final bounded construction exposes nonlinear FAT sizing (2026-08-12)

The frozen compiler/hash and the 151 MiB sizing plan were accepted. The single
strict cached build linked the 479 KiB kernel again (`4 compiled, 294 cached`).
Media construction then failed before QEMU with a different FAT geometry:

```text
fat_capacity status=fail payload=structural bytes=25125512
required_clusters=12269 allocated_clusters=69569
capacity_clusters=77153 cluster_bytes=2048 minimum_image_mb=161
disk image too small for payload set
```

At 128 MiB the builder used 1 KiB clusters and reported a 135 MiB minimum. At
151 MiB it selected 2 KiB clusters and reported a 161 MiB minimum. Therefore
the recorded minimum plus fixed headroom model is not monotonic across FAT
cluster-size thresholds and is not yet a valid deterministic preflight.

Retained logs:

- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-final-20260812/x86_64/kernel-build.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-final-20260812/x86_64/image-build.log`

No retry and no QEMU process were launched. Resume by adding a construction-
free geometry calculator (or a bounded deterministic size search) that computes
cluster size, data-cluster capacity, and structural allocation demand for each
candidate, then selects the first fitting size plus bounded reserve. The current
151 MiB x86_64 selection must not be treated as sufficient. Diagnostic RED.

## Geometry-aware no-write capacity planner (2026-08-12)

The C media owner now supports `SIMPLEOS_DISK_CAPACITY_PLAN=1`: it reads the
authoritative payload set and executes the exact FAT reservation sequence, but
does not allocate an image buffer or copy payload bytes. The shell owner uses
failure receipts as deterministic jumps under the existing minimum and 512 MiB
hard maximum. The rebuild wrapper plans before construction, records the plan
hash, and performs only one actual payload-write pass at the selected size.

An exact no-write x86_64 plan against the already-built kernel proved the
stable transition:

```text
151 -> 161 -> 162 -> 163 -> 164 -> 165 -> 166 -> 167 MiB
fat_capacity status=pass selected_image_mb=167
allocated_clusters=85311 capacity_clusters=85329 cluster_bytes=2048
```

No image path was created. Evidence is retained at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/x86_64-geometry-plan-20260812/capacity-plan.log`
(SHA-256 `0ffe064c0b7bfd7b17724b9b71533e5cd0a00f8b9b827d5f145bc5fdb4efbd01`).
The static plan labels 151 MiB as `image_initial_candidate_mb` and marks
`geometry_plan_required=true`; only the no-write planner publishes final
`image_selected_mb`. Self-tests cover the 128/1 KiB to 151/2 KiB to 161 MiB
transition, stable 167 MiB selection, too-small input, bounded headroom, and
stable receipts. C99 syntax, shell syntax, plan output, and diff checks pass.
No kernel build or QEMU boot was performed.

## 167 MiB construction succeeds; strict ELF gate blocks boot (2026-08-12)

The fresh bounded continuation successfully completed the cached strict build,
the exact no-write geometry plan, and one media construction. The retained
receipt records `image_selected_mb=167`, compiler hash
`2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`, kernel
SHA-256 `acc83b1039138084c1e14f040f1ae67a49f847b00ab0dd5b2e094f9d70bf00b9`,
and image SHA-256
`492bcf1141497568d3aac775cbf3c771a883beba3c7312ff8e31d3b3f8eb8a8c`.

The first post-construction static gate then failed:

```text
[x86-kernel-elf] ERROR: kernel contains a defined weak symbol
```

The retained ELF has zero strong undefined symbols but 688 unique defined weak
symbols. They include syscall handlers, fault hooks, `rt_memcpy`/`rt_memset`,
module initializers, and module globals. Enabling
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` would make the checker accept this shape,
but that override denotes a deliberately incomplete freestanding build and is
not valid for the strict real-exec lane. No nonce clone and no QEMU process were
created.

Artifacts and logs:

- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-geometry-live-20260812/x86_64/kernel.elf`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-geometry-live-20260812/x86_64/disk.img`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/x86_64-real-exec-geometry-live-20260812/x86_64/receipt.env`

Resume by classifying the linker’s weak boot-alias policy: real selected Simple
definitions must be emitted/promoted as strong, while genuinely optional
fallbacks must be eliminated from this entry closure or rejected. Do not relax
the checker or enable the incomplete-stub override. Diagnostic RED.

## Current-worktree lifecycle regression and recovery (2026-08-12)

A concurrent overwrite removed the earlier scheduler-owned launcher and put
the canonical entry back on unconditional SMF package-probe PASS. The exact
original patch was recovered from its Codex rollout receipt and restored:
validated TaskId/address-space generation/expected CR3 token installation,
CR3-authenticated syscall 60 and exit, one-shot result consumption, exact child
exit/status validation, and reap. The canonical entry again performs the live
nonce read, `/SYS/APPS` dirent walk, and `/FSEXEC.ELF` scheduler-owned handoff.

The matrix descriptor now requires the truthful listing plus target-produced
nonce stdout, `FS_PROGRAM_END rc=37 reaped=true`, and final PASS markers. New
`check-x86-64-real-fs-exec-wiring.shs` source sabotage prevents the synthetic
package-probe entry from silently returning. Static wiring/listing and C syntax
checks pass; a fresh admitted build and QEMU run are still required, so the row
remains RED rather than promoted.
