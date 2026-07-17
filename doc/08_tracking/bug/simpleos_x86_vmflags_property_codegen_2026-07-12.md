# SimpleOS x86 VmFlags property-style lowering failure

## Status

Source fix implemented and verified (2026-07-12). Fresh x86 Cranelift build reports zero failed/skipped files for paging/VMM modules.

## Evidence

The Cranelift build reports:

```text
arch/x86_64/paging.spl: cannot infer field type: VmFlags.writable
memory/vmm.spl: cannot infer field type: VmFlags.writable
arch_adapt/x86_64/paging.spl: 7 function bodies failed
```

`VmFlags` stores only `bits` and exposes `present()`, `writable()`, `user()`,
`write_through()`, `cache_disable()`, and `no_execute()` methods. The failing
files still use property syntax and construct obsolete named boolean fields.
`memory/vmm.spl::_flags_to_pte_bits` already documents and demonstrates the
correct explicit-method form.

## Fix

Both concrete x86 paging implementations now call the existing `VmFlags`
accessors. Their W^X branches preserve the complete bitfield and add
`VM_NO_EXECUTE` with `VmFlags(bits: flags.bits | VM_NO_EXECUTE)`, matching the
existing address-space implementation. No adapter or stub fallback changed.

Both focused Simple source checks pass. The isolated Rust seed/runtime and a
fresh Stage 2 compiler were rebuilt; Stage 2 SHA-256 is
`1f784c159f755efdc125e9339f26b1eab839ff4ff67f4a97771c6be34bb26049`.
The next x86 build must report zero failed/skipped files before the ELF or QEMU
evidence is accepted.
