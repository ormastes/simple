# SOSIX executable gates blocked by incomplete runtime wide-integer merge

**Date:** 2026-08-11  
**Status:** open, concurrent-owner integration required

## Impact

The SOSIX FS v1 executable specifications and release-lineage QEMU reruns need
a deployed pure-Simple compiler. The single cache-preserving bootstrap attempt
failed at Stage 2 and correctly refused Rust-seed fallback.

## Retained evidence

Log:
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`

Initial failures were:

- conflicting `rt_dir_create` declarations;
- missing `runtime_terminal_signal_scope_impl.h`.

Another active runtime lane changed `runtime_native.c` while this failure was
being diagnosed: it split terminal ownership into `runtime_terminal.c`, removed
the missing include, and separated the C-path directory helper. One allowed C
syntax probe then passed both initial sites and reached a later incomplete
wide-integer merge.

The first remaining hard failure is at `runtime_native.c:3202`:

```text
unknown type name 'RtCoreUInt'
implicit declaration of function 'rt_core_as_heap_uint'
```

The file's current owner defines `RtCoreWideInt` and
`rt_core_as_heap_int`, while equality, dictionary-key, and typed-word helpers
still reference the former unsigned representation. There is also an earlier
implicit `rt_value_u64` warning. This is semantic integration work, not a safe
mechanical rename: signed wide integers and full-range `u64` values have
different comparison and hashing requirements.

## Resume gate

The runtime owner must finish and test one coherent representation across:

- boxing/unboxing;
- generic equality;
- array equality with packed `u64` elements;
- dictionary canonicalization, hashing, and equality;
- full-range `u64` typed-word conversion.

Then run one focused C runtime check. Only after it passes, resume the existing
bootstrap cache with:

```sh
env SIMPLE_NO_STUB_FALLBACK=1 scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

Do not delete `build/bootstrap/native_cache`, and do not accept a Rust-seed
result as SOSIX or QEMU release evidence.
## Follow-up convergence probe

A later, single C syntax probe retained under
`build/native_probe/runtime-bootstrap-convergence/` confirms the concurrent
runtime merge is still internally inconsistent. The first hard error is now
`runtime_native.c:2191`, where `rt_value_u64` is undeclared. Stale
`RtCoreUInt`/`rt_core_as_heap_uint` uses also remain at lines 3202, 3287, 3327,
and 7662 while only the replacement `RtCoreWideInt`/`rt_core_as_heap_int`
model is defined. No second bootstrap was attempted because the prerequisite C
syntax gate was red.
