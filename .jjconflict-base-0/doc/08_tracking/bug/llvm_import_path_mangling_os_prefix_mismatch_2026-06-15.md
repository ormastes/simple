---
id: llvm_import_path_mangling_os_prefix_mismatch_2026-06-15
status: INVESTIGATING
severity: high
discovered: 2026-06-15
discovered_by: SimpleOS riscv64 LLVM build (`bin/simple os build --scenario=rv64-base`)
related: src/compiler_rust/compiler/src/pipeline/native_project/imports.rs
related: src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs
related: src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs
related: src/compiler_rust/compiler/src/pipeline/native_project/linker.rs
related: src/os/kernel/boot/tcp_baremetal_min.spl
related: src/os/kernel/log/klog_api.spl
related: src/os/kernel/fs/fat32.spl
---

# LLVM rv64 link fails: cross-module call references `os__kernel__…` but definitions emit bare/weak names

## Summary

Building SimpleOS riscv64 with the LLVM backend
(`bin/simple os build --scenario=rv64-base`) fails at link time. Codegen
succeeds; `ld.lld` reports undefined symbols such as:

```
ld.lld: error: undefined symbol: os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind
ld.lld: error: undefined symbol: os__kernel__log__klog_api__log_raw_println
ld.lld: error: undefined symbol: os__kernel__fs__fat32__parse_bpb
ld.lld: error: --defsym:1: symbol not found: os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind
```

The **caller** objects reference the fully module-qualified symbol
`os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind`, but the **defining**
object emits the function under a *different* name.

## Root Cause (corrected — NOT a source-root `os` prefix bug)

The original hypothesis was that definitions are source-root-relative
(`kernel__…`) while references add a spurious `os__` segment. Direct `nm`
inspection of the freshly built objects disproves that. Source dirs are
`--source build/os/generated --source src --source examples`, so
`module_prefix_from_path("src/os/kernel/boot/tcp_baremetal_min.spl", "src")`
correctly yields prefix `os__kernel__boot__tcp_baremetal_min` for BOTH the
definition pass and the import-map / caller pass. There is no `os`-segment
divergence.

The real divergence: **the affected functions' DEFINITIONS are emitted with
their BARE, weak name, while cross-module CALLERS resolve the call to the
fully-qualified import-map name.**

`nm` of the object compiled from `tcp_baremetal_min.spl` (`mod_*.o`):

```
T os__kernel__boot__tcp_baremetal_min__boot_tcp_probe_bind   # normal fn: qualified, External
W rt_io_tcp_bind                                             # @export fn: BARE, WeakAny
W rt_io_tcp_accept_timeout
W log_raw_println                                            # ambiguous fn: BARE, WeakAny
```

Two distinct mechanisms produce bare definition symbols:

1. **`@export` / `#[export]` functions** (`rt_io_tcp_bind`,
   `rt_io_tcp_accept_timeout`, …). Parsed as a function attribute `"export"`.
   These get a bare C-ABI symbol on the definition side
   (LLVM `declare_function_with_linkage`: a name with no `__` →
   `Linkage::WeakAny`, i.e. bare weak). But `build_import_map`
   (`imports.rs`) records them under the *prefixed* name
   `os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind`, so the caller's
   `use os.kernel.boot.tcp_baremetal_min` resolves the call to the prefixed
   symbol — which no object defines.

2. **Ambiguous functions** (`log_raw_println` is defined in 10 modules,
   `rt_io_tcp_bind` in 5). These also resolve to a bare/weak definition,
   while callers still bind to a prefixed import-map entry.

The LLVM definition pass and call pass both use
`use_map.get(name).or(import_map.get(name)).unwrap_or(name)`
(`backend_core.rs` declare pass + `functions.rs` body pass + `calls.rs`
call site). The mismatch is that the definition side ends up bare while the
import map hands callers the prefixed name.

`parse_bpb` (defined in exactly one module, plain `fn`) appears in the same
undefined list; it is referenced as `os__kernel__fs__fat32__parse_bpb`.

## Reproduction

```
bin/simple os build --scenario=rv64-base 2>&1 | tee /tmp/rv64_alpha.log
# native-build cmd:
#   simple native-build --source build/os/generated --source src --source examples \
#     --backend llvm --opt-level=aggressive --entry-closure \
#     --entry src/os/kernel/arch/riscv64/boot.spl --target riscv64-unknown-none \
#     -o build/os/simpleos_riscv64.elf --linker-script .../linker.ld
```

## Fix

Implemented in the Rust seed freestanding linker stage
(`pipeline/native_project/linker.rs`), canonicalizing references toward the
bare definitions without changing any definition mangling (so targets that
already link — x86_64/arm64 — are unaffected because they emit no such dangling
references):

1. New `freestanding_qualified_to_bare_defsyms`: for every undefined
   `PREFIX__SUFFIX` reference for which no object defines `PREFIX__SUFFIX` but
   some object defines the bare `SUFFIX`, emit `--defsym=PREFIX__SUFFIX=SUFFIX`.
   This bridges the qualified caller reference onto the bare `@export`/ambiguous
   definition. Wired into both the direct-`lld` and `cc`-driven freestanding
   link command branches.

2. Hardened the pre-existing `freestanding_weak_boot_defsyms`: it built
   `simple_defined` with an unconditional insert that included undefined (`U`,
   weak-undefined `w`/`v`) symbols, so it could alias a boot-weak symbol onto a
   name that nothing defines — the source of the
   `ld.lld: error: --defsym:1: symbol not found: …` class. Now undefined kinds
   are excluded from both `simple_defined` and `simple_strong_defined`.

Unit test: `test_freestanding_qualified_to_bare_alias_bridges_export_symbol`
(`pipeline/native_project/tests.rs`).

## Separate blocker: `parse_bpb` (NOT the mangling bug)

`os__kernel__fs__fat32__parse_bpb` is undefined for an unrelated reason:
`src/os/kernel/fs/fat32.spl` fails to compile and is skipped:

```
src/os/kernel/fs/fat32.spl: llvm codegen: semantic: LLVM verification failed:
  "Incorrect number of arguments passed to called function!
   %mcall_direct = call i64 @os__kernel__boot__c_nvme_adapter__CNvmeBlockAdapterFs.read_sector(i64, i64, i64)"
```

Root cause is a stale call site in `fat32.spl:245`:
`dev.read_sector(root_lba + sec_idx.to_u64(), sec_buf)` passes TWO arguments,
but the `BlockDevice::read_sector(lba: u64) -> Result<[u8], text>` trait/impl
(`c_nvme_adapter.spl:47`) takes ONE. Every other call site (212, 349, 447, …)
uses the 1-arg form. Because the whole file is dropped, `parse_bpb` (and the
rest of fat32) emits no symbol at all, so the qualified→bare bridge has nothing
to alias to. This must be fixed in the `.spl` source (a one-line correction of
the line-245 call), and is outside this mangling fix's locus.

## Notes

- A separate, concurrent fix addresses `rt_bytes_alloc` in
  `freestanding_runtime.c`; that symbol is unrelated to this mangling bug.
