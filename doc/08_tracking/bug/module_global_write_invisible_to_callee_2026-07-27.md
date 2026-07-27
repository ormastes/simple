# Module-global write inside a `fn` is invisible to every callee (interpreter)

**ID:** module_global_write_invisible_to_callee_2026-07-27
**Status:** OPEN — root-caused, not fixed
**Severity:** Critical (silent wrong results; no diagnostic)
**Component:** Rust seed interpreter — `src/compiler_rust/compiler/src/interpreter_call/**`
**Engines:** interpreter ONLY. JIT (cranelift) is correct.
**Found by:** lane SMPFIX (kernel panic in `percpu_init`), root-caused by lane GLOBAL.

## Summary

When a function assigns to a module-level global and then calls another
function, the callee reads the **pre-call snapshot**, not the write. The write
becomes visible only after the writing function **returns**.

This is **not** limited to arrays, to `.push`, to indexed assignment, or to the
spec runner. Under the interpreter it affects **every** assignment form and
**every** global type. It is invisible — no warning, no error.

The original report framed this as "works from `fn main()`, fails in a spec".
That framing is an artifact of engine selection, not of the calling context:
`bin/simple run` defaults to the **JIT** (which is correct), while the spec
runner always executes on the **interpreter** (which is broken). Forcing
`SIMPLE_EXECUTION_MODE=interpreter` reproduces the defect from a plain
`fn main()` with no spec runner involved.

## Truth table

Repro sources: `build/global_repro/`. Binary for every row:
`bin/release/x86_64-unknown-linux-gnu/simple` (the Rust bootstrap **seed** —
it prints `WARNING: this Rust-built Simple binary is a bootstrap seed only`;
that is the binary `bin/simple` currently symlinks to).

`writer sees` = probe printed inside the writing function immediately before it
calls the helper. `callee sees` = probe printed inside the helper.

| # | Global | Write form | Writer/global location | Driver | Engine | writer sees | callee sees | Verdict |
|---|--------|-----------|------------------------|--------|--------|-------------|-------------|---------|
| A | `[i64]` | `g = g.push(i)` in `while` | same module as `main` | `fn main()` | JIT | len 4 | len 4 | PASS |
| B | `[i64]`+`i64` | `g = [..]`, `g = 99` | same module as `main` | `fn main()` | JIT | 4 / 99 | 4 / 99 | PASS |
| G | `[i64]`+`i64` | `g = g.push(i)` in `while` | imported module `gmod` | `fn main()` | JIT | len 4, n 4 | len 4, n 4 | PASS |
| H | `[i64]`+`i64` | `g = [..]`, `g = 99` | imported module `gmod` | `fn main()` | JIT | len 4, n 99 | len 4, n 99 | PASS |
| G' | `[i64]`+`i64` | `g = g.push(i)` in `while` | imported module `gmod` | `fn main()` | **interp** | len 4, n 4 | **len 0, n 0** | **FAIL** |
| H' | `[i64]`+`i64` | `g = [..]`, `g = 99` | imported module `gmod` | `fn main()` | **interp** | len 4, n 99 | **len 0, n 0** | **FAIL** |
| E | `[i64]`+`i64` | `g = g.push(i)` in `while` | imported module `gmod` | spec `it` | **interp** | len 4, n 4 | **len 0, n 0** | **FAIL** |
| F | `[i64]`+`i64` | `g = [..]`, `g = 99` | imported module `gmod` | spec `it` | **interp** | len 4, n 99 | **len 0, n 0** | **FAIL** |
| 1 | `i64` | `g_n = 42` (bare, top level) | imported module `gtf` | spec `it` | **interp** | 42 | **0** | **FAIL** |
| 2 | `[i64]` | `g_arr = [7,7,7,7]` (bare) | imported module `gtf` | spec `it` | **interp** | 7 | **0** | **FAIL** |
| 3 | `[i64]` | `g_arr[2] = 55` (indexed) | imported module `gtf` | spec `it` | **interp** | 55 | **0** | **FAIL** |
| 4 | `[i64]` | `g = g.push(..)` in `while` | imported module `gtf` | spec `it` | **interp** | len 7 | **len 4** | **FAIL** |
| 5 | `i64` | `g_n = 777` inside `if`/`while` | imported module `gtf` | spec `it` | **interp** | 777 | **0** | **FAIL** |

In every FAIL row the value **is** correct after the writer returns — the write
is not lost, only **deferred**.

### Axes that do NOT matter
Global type (scalar / array), assignment target form (bare identifier / indexed
/ nested in `if`/`while`), same-module vs imported module, and spec-runner vs
plain `main()` are all irrelevant. Rows 1–5 fail uniformly.

### The one axis that matters
**Engine.** JIT correct, interpreter broken. Secondary: the writer must be a
normal `fn`. A write performed directly inside a BDD colon-block (`it:` body)
*is* synced per statement — see mechanism.

### Separate defect found in passing
Same-module module-level `var` under the interpreter is rejected as immutable:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/global_repro/main_ctl.spl
error: semantic: invalid assignment: cannot reassign to immutable variable 'g_arr'
```

The identical file runs correctly on the JIT. Cross-module `var` writes are
accepted by the interpreter. Filed here as a note; deserves its own bug.

## Minimal repro

`build/global_repro/gmod.spl` (module owning the globals):

```
var g_arr: [i64] = []
var g_n: i64 = 0

fn helper_reads():
    print("    [helper] arr_len=", g_arr.len(), " n=", g_n)

fn writer_assign():
    g_arr = [10, 11, 12, 13]
    g_n = 99
    print("  [writer] before call arr_len=", g_arr.len(), " n=", g_n)
    helper_reads()
```

`build/global_repro/main_cross.spl`:

```
use build.global_repro.gmod.{writer_assign}

fn main():
    writer_assign()
```

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/global_repro/main_cross.spl
  [writer] before call arr_len= 4  n= 99
    [helper] arr_len= 0  n= 0        <-- WRONG
```

Drop `SIMPLE_EXECUTION_MODE` (JIT) and the helper prints `4 / 99`.

## Mechanism

Module globals are **not** shared storage in the interpreter. They are
thread-local maps that get **copied into a callee's env at call entry** and
**written back only on return**.

Storage: `src/compiler_rust/compiler/src/interpreter_state.rs:213-222` —
`MODULE_GLOBALS` (flat/legacy), `MODULE_GLOBALS_BY_OWNER` (live per-module),
`MODULE_GLOBALS_INITIAL_BY_OWNER`, `MODULE_ENV_BY_OWNER`,
`MODULE_GLOBAL_BINDINGS_BY_OWNER`.

1. **Copy-in at call entry** —
   `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:47`
   `captured_env_with_live_globals()`. At `:66-73` it clones
   `MODULE_GLOBALS_BY_OWNER[owner]`, and at `:100-102`:

   ```rust
   base.extend(imported_globals);
   base.extend(owner_globals);      // <-- extends LAST: overrides the live captured env
   Env::with_base(Arc::new(base))
   ```

   `owner_globals` is the **committed** map. Because it extends last, it
   overwrites any fresher value the caller's env carried. This is the line that
   makes the callee read the stale snapshot.

2. **Write-back only on return** —
   `function_exec.rs:105` `sync_owned_captured_globals()`. At `:114-128` it
   scans the returning function's `local_env.overlay_entries()` and re-inserts
   them into `MODULE_GLOBALS_BY_OWNER`; `:143-150` mirrors into the flat map;
   `:151-158` refreshes the caller's env (only when
   `CURRENT_EXEC_MODULE == owner`). Call sites are strictly paired around the
   body: entry `:644, :708, :965, :1056, :1149`, exit `:691, :732, :1013,
   :1081, :1163`.

   So during the writer's body, `MODULE_GLOBALS_BY_OWNER[owner]` still holds
   the pre-call value. Every callee invoked mid-body copies that stale value in
   at step 1.

3. **Why the BDD colon-block path is exempt — and why a `fn` is not.**
   There *is* a per-statement seed/sync that would fix this, but it exists in
   only one executor. `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs:56`
   `seed_module_global()` and `:70` `sync_module_global()` are invoked from the
   `Node::Assignment` arm at `:311-312` / `:321-322` — and that arm lives inside
   **`exec_block_closure()`** (declared `block_execution.rs:206`, "Execute a
   block closure (BDD DSL colon-block) against a fresh scope"), plus its twin
   `exec_block_closure_mut()` at `:1070` (`:1121` / `:1131`).

   The **function-body** executor is a different function —
   `src/compiler_rust/compiler/src/interpreter/block_exec.rs:167`
   `exec_block_fn()` — and it has **no** per-statement global seed/sync. A
   repo-wide grep confirms `seed_module_global` / `sync_module_global` have
   exactly four call sites, all in `block_execution.rs` (plus
   `interpreter/place.rs:227,239`), none in the `fn`-body path.

   **Root cause, one sentence:** the per-statement module-global write-through
   was implemented for BDD colon-blocks only; inside a normal `fn` the write
   lives in a local env overlay and is published to `MODULE_GLOBALS_BY_OWNER`
   only by `sync_owned_captured_globals` on return, while every callee's
   `captured_env_with_live_globals` re-reads that not-yet-updated map and
   `base.extend(owner_globals)` clobbers anything fresher.

4. **Additional silent-drop guards in the same code.** Both write-back paths
   discard rather than create: `sync_owned_captured_globals` skips a name when
   `!owner_globals.contains_key(name)` (`function_exec.rs:118`), and
   `sync_module_global` only writes `if globals.contains_key(&name)`
   (`block_execution.rs:325`). A global not already present in the owner map has
   its write dropped entirely.

5. **Contrast — JIT is correct** because it never uses this model: globals are
   real `.data`/`.bss` slots.
   `src/compiler_rust/compiler/src/codegen/cranelift_emitter.rs:96-120`
   (`emit_global_load`) / `:121-136` (`emit_global_store`) via `ctx.global_ids`
   + `declare_data_in_func`. One storage location, no copy, no write-back.

6. **Pure-Simple interpreter uses a different (sound) model** — a chained
   globals hash map that `env_lookup`/`env_assign` fall through to, with no
   copy/write-back: `src/compiler/10.frontend/core/interpreter/env.spl:17-21`,
   `:127-135`, `:155-163`, `env_define_global` at `:167`. This bug is specific
   to the Rust seed. Note the pure-Simple MIR path carries a related documented
   hazard at `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:185-191`
   ("bare `.push()` on a module global silently drops elements, 81 of 842").

## Blast radius

Scan over owned `.spl` under `src/**` (vendored paths excluded), looking for a
module global mutated inside a `fn` that then calls another function.

| Metric | Count |
|---|---|
| `.spl` files scanned | 13,738 |
| Files with >=1 hazardous mutation | 271 |
| Hazardous mutation sites | 2,746 |
| — indexed assign `G[i] = ...` | 1,796 |
| — field assign `G.f = ...` | 55 |
| — bare mutating call `G.push/append/insert/remove/clear/set(...)` | 895 |
| **Exploitable (a call follows in the same fn)** | **1,446 in 208 files** |
| Exploitable in kernel/sched/alloc/mem/driver/security/crypto/capability/compiler | 910 (100 files) |

By area: `src/compiler/` 596, `src/lib/` 366, `src/os/` (non-kernel) 251,
`src/os/kernel/` 192, `src/app/` 34.

**This is a LOWER BOUND.** The scan targeted non-bare write forms
(`G[i] =`, `G.f =`, bare `G.push(...)`), because those were the initially
suspected shape. Rows 1, 2 and 5 of the truth table prove that plain
`G = expr` fails identically, so the true hazardous population is larger.

### Worst instances

1. `src/os/kernel/memory/heap.spl:182` — `g_heap.total_allocated` updated in
   `heap_alloc` before onward calls; allocator accounting invisible to callees.
2. `src/os/kernel/memory/pmm.spl:340` — `g_page_refcounts[..]` zeroed in
   `_pmm_free_page_index` before further calls; double-free / UAF window.
3. `src/os/kernel/ipc/capability.spl:1085` — `g_task_vmspaces[..]` written in
   `register_task_vmspace`; **security-relevant** task→vmspace binding.
4. `src/os/kernel/ipc/syscall_spm.spl:48` — `_priv_table.set(target_id, mask)`
   in `_handle_privctl`; **privilege-mask change not seen by callees in the
   same syscall**.
5. `src/os/kernel/scheduler/process_table_extended.spl:81` —
   `_pt_ext_pid_list.push(..)` in `pt_ext_register`; scheduler table stale
   mid-registration.
6. `src/os/kernel/fd_table.spl:452` — `fd_fd_flags[..]` CLOEXEC set in
   `fd_dup_from`; fd leak across exec.
7. `src/os/kernel/lifecycle/task_cleanup.spl:148` — `task_res_type[..]` marked
   `RES_NONE`; teardown still sees live slots.
8. `src/os/kernel/arch/x86_64/paging.spl:222,230` — `g_vmm.hhdm_offset` /
   `g_vmm.pml4_phys` set in `vmm_init`, then mapping helpers read the old
   struct (same shape in riscv32/riscv64/x86_32 `paging.spl`).
9. `src/os/kernel/arch/riscv64/hal_smp.spl:159` — `HAL_SMP_BOOT_ARGS[..]`
   stored before starting the AP; AP may read stale boot args.
10. `src/os/kernel/memory/vmm_shared.spl:129` — `_shp_obj.push(..)` in
    `_shm_intern_page`; interning table stale for nested lookups.
11. `src/os/kernel/ipc/message_buffer.spl:357` — `buffer_pool_owner[..]`
    reassigned in `ipc_send_buffer`; ownership race in nested IPC.
12. `src/os/kernel/interrupts/irq_routing.spl:37` — `route_notif_id[..]`
    IRQ→notification route.
13. `src/os/kernel/loader/elf_loader.spl:307` — `g_staged_x64_offsets.push(..)`
    consumed by later staging calls.
14. `src/os/kernel/loader/fs_exec_resolve.spl:80` — `g_fs_exec_cache_name`
    push; cache-miss loops downstream.
15. `src/compiler/10.frontend/core/alloc_inference.spl:55` — `ai_direct_alloc`
    pushed then recursed into; wrong allocation inference.

Also: `src/os/kernel/net/{loopback_socket,rt_net_socket_facade,tcp_shim_state}.spl`,
`src/os/kernel/pipe_compat.spl:108`,
`src/lib/nogc_async_mut_noalloc/baremetal/{process_table,vm_fault,kevent,namespace}.spl`.

**Known real damage:** `percpu_init` in `src/os/kernel/smp/percpu.spl` filled
`g_percpu` with 32 entries, then called `percpu_store_entry`, which observed an
empty global and grew it to length 1. That 1-element table was published and
every `cpu_id >= 1` access trapped — a kernel panic. Already worked around in
that file (see the comment at `percpu.spl:39-45`).

## Workaround (already applied in `percpu.spl`)

**Build in a local, publish once.** Never let a callee observe a
partially-written global:

```
fn percpu_init(count: i64):
    var table: [PerCpu] = []          # accumulate in a LOCAL
    var i = 0
    while i < count:
        table = table.push(make_entry(i))
        i = i + 1
    g_percpu = table                   # single publish
    g_percpu_initialized = true
    # do NOT call a helper that reads g_percpu before this point
```

Rule: a function that writes a module global must not call any function that
reads it. If it must, pass the value as a parameter instead of re-reading the
global.

## Fix sketch (NOT applied)

`src/compiler_rust/**` currently has a live lane (CAPFIX2). **Do not race it** —
land this only after coordinating.

Options, cheapest first:

- **(a) Extend the existing write-through to `fn` bodies.** Lift the
  `Node::Assignment` seed/sync from `block_execution.rs:311-322` into
  `interpreter/block_exec.rs:167 exec_block_fn`. Cheap and local, but only
  covers bare-identifier `Expr::Identifier` targets (the arm at
  `block_execution.rs:306-308` returns `None` for `Expr::Index` /
  `Expr::FieldAccess`), so rows 3 and 4 would still fail. **Partial fix.**

- **(b) Publish on every write, whatever the target form.** Resolve the root
  identifier of the assignment place (there is already a place model —
  `interpreter/place.rs:227,239` calls `sync_module_global`) and sync after
  every statement that mutates a global root, including index/field writes and
  bare mutating method calls. Covers all rows. Medium risk.

- **(c) Correct fix — stop copying.** Make module globals shared mutable
  storage (`Rc<RefCell<Value>>` slots in the owner map) so reads and writes hit
  one location, matching both the JIT (`.data` slots) and the pure-Simple
  interpreter (chained globals map). Delete `captured_env_with_live_globals`'s
  `base.extend(owner_globals)` copy-in and `sync_owned_captured_globals`
  entirely. This is the model the other two engines already use. Highest value,
  highest risk — needs its own lane.

Whichever is chosen, also remove the two silent-drop guards in §Mechanism item 4
(`function_exec.rs:118`, `block_execution.rs:325`): a write to a global missing
from the owner map should create the entry or raise, never be discarded.

## Regression spec (to add with the fix)

Port `build/global_repro/gtf.spl` + `gtf_spec.spl` (rows 1-5) into
`test/01_unit/compiler/module_global_write_visibility_spec.spl`. It must run on
the **interpreter** to be meaningful — the spec runner already does, but assert
it rather than assume. A JIT-only run is a false green: every row passes there.

## Artifacts

- `build/global_repro/gmod.spl`, `gtf.spl` — modules owning the globals
- `build/global_repro/main_ctl.spl` — same-module `fn main()` control
- `build/global_repro/main_cross.spl` — cross-module `fn main()` control (rows G/H, G'/H')
- `build/global_repro/target_form.spl` — target-form matrix under `fn main()`
- `build/global_repro/g_spec.spl`, `g2_spec.spl`, `g3_spec.spl`, `gtf_spec.spl` — spec-context rows
- `build/global_repro/out_*.txt` — captured transcripts

## Related

- `doc/08_tracking/bug/interp_module_global_stale_read_in_spec_blocks_2026-07-05.md` — OPEN, the spec-block-visible face of this defect
- `doc/08_tracking/bug/seed_interp_defer_lazy_imports_module_globals_2026-07-24.md` — FIXED `2cbebf1bcb05`; added the flat-map mirror in `sync_owned_captured_globals`
- `doc/08_tracking/bug/cross_import_const_no_hir_linkage_2026-07-25.md` — OPEN, cross-import consts
- `doc/08_tracking/bug/selfhost_two_hop_field_method_mutation_lost_2026-07-27.md` — sibling place-model defect
