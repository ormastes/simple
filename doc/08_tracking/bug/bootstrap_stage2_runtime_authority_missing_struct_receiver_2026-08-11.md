# Bootstrap stage 2 runtime authority missing struct receiver guard

Date: 2026-08-11  
Status: SOURCE FIX VERIFIED; canonical bootstrap publication pending

## Symptom

An isolated incremental Cranelift bootstrap aborted while building stage 2:

```text
PANIC missing runtime fn 'rt_struct_receiver_valid' in run_native_build_bootstrap
```

Evidence is retained at
`build/bootstrap-server-recovery/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.

## Cause

The C implementation and archive ownership were present, but the Rust runtime
provider generator used a physical-line scanner that recognized a C function
definition only when its opening `{` appeared at the end of the same line.
`rt_struct_receiver_valid` has a multiline signature, so it was silently omitted
from generated `RUNTIME_SYMBOL_ENTRIES`. Cranelift's JIT therefore could not
resolve the helper even though `runtime_memory.c` was linked.

The stale stage-2 authority preserves that generated-table defect. Merely
reusing it cannot recover the symbol.

The source fix replaces the line scanner with a declaration-aware scanner,
lists the struct allocator and validator in the common runtime registry, and
tests their generated pointers as one callable ownership pair.

### Source verification

The focused runtime-table test passed on 2026-08-11:

```text
runtime_symbol_table_keeps_struct_allocator_and_receiver_validator_paired ... ok
test result: ok. 1 passed; 0 failed
```

This proves current Rust runtime-table generation and C provider behavior. It
does not admit any previously produced stage-2/stage-3 executable.

## Required recovery and acceptance

1. Complete one canonical `--full-bootstrap` so the seed and frozen runtime
   authority are rebuilt from the source revision containing the scanner fix.
2. Produce admitted stage 2 and stage 3 executables and a canonical deployment
   receipt.
3. Require the compiler selector's real-work probe to accept the deployed
   pure-Simple compiler.
4. Only then retry strict server native builds with
   `SIMPLE_NO_STUB_FALLBACK=1`.

An incremental retry against the same stale authority is prohibited because it
cannot add the missing export and would repeat the identical failure.

## Fail-fast probe

`test/04_smoke/bootstrap_struct_receiver_guard.spl` performs a mutable class
field write and read, the smallest known source surface that requires
`rt_struct_receiver_valid`. The isolated checker
`scripts/check/check-bootstrap-stage2-struct-receiver.shs` builds and executes
that fixture with the candidate stage 2 compiler and its exact runtime.

The existing `windows_native_hello.spl` capability probe is insufficient: it
can pass while receiver validation is absent. The canonical bootstrap script
must run the new probe before stage 3 admission. That script currently has an
unrelated active storage-root edit, so this lane deliberately did not modify or
combine it.

### Real candidate result

The checker was run once against the 130,214,720-byte stage 2 candidate in the
isolated stage3-recovery worktree and its exact stage2 runtime archive. It
failed in 2.3 seconds while compiling the fixture:

```text
missing runtime fn 'rt_struct_receiver_valid' in main
```

This is an authoritative rejection of that candidate, not a server-build
failure and not a passing compiler receipt. The short probe replaces a
multi-minute server closure as the admission oracle for this runtime surface.

## Follow-up: allocator and gate invocation defects

After using a freshly rebuilt seed, the smoke reached
`rt_struct_receiver_valid` but trapped with `invalid field receiver`.
Disassembly proved Rust Cranelift allocated the user struct through `rt_alloc`;
the bounds guard therefore correctly found no `rt_struct_alloc` ownership
record. `GcAlloc` now selects the paired allocator for user-defined
`TypeId >= 16`. Ordinary struct construction and aggregate block copies also
use `rt_struct_alloc`; raw closure/tuple storage remains on `rt_alloc`.

The checker also passed an archive filename to `--runtime-path`, although that
CLI option requires a directory. It now normalizes archive inputs to their
containing directory, avoids incompatible `--mode dynload`, and reports a
signalled probe execution instead of exiting silently under `set -e`.

### Corrective verification

The focused allocator regression passed 1/1. A cached diagnostic Rust compiler
built from the corrected sources then compiled, statically linked, and executed
the receiver fixture against the freshly built runtime archive; the gate
reported `bootstrap_stage2_struct_receiver=PASS`.

This verifies the source-level runtime export and allocation pairing only. It
does not admit or publish a pure-Simple stage 2/stage 3 compiler. Canonical full
bootstrap, selector acceptance, and deployment receipt remain required before
the server native-build gates may run.

### Canonical bootstrap attempts

A fresh-authority full bootstrap removed the former missing-symbol panic and
produced a Stage 2 that compiled the receiver fixture. That pre-LLVM-fix
candidate still trapped with `invalid field receiver`. After correcting the
LLVM allocation sites, a second full bootstrap was safely refused before
publication because another active lane changed Rust inputs during the build.
The consistency guard behaved correctly; no post-fix Stage 2/Stage 3 or 8K
performance claim is made from these attempts.

### Final bounded recovery cycle

After Rust sources remained stable for more than three minutes, the third and
final permitted full-bootstrap cycle rebuilt the fixed seed but failed while
building `simple-native-all`. The runtime currently re-exports three absent
symbols: `objects::rt_expect_or_trap`, `sffi::rt_value_as_u64`, and
`sffi::rt_value_u64`. These belong to concurrent runtime work and were not
patched or folded into this rendering lane. Per the three-cycle guard, no
further bootstrap retry was attempted. The LLVM allocator fix remains locally
verified, but canonical publication and all native 8K reruns remain pending.
