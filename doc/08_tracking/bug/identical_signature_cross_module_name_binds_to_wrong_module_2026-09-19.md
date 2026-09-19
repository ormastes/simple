# Same name, same signature, two modules: a caller can bind to the wrong one (silent, no warning)

Status: OPEN (recorded, not fixed)
Found: 2026-09-19, lane C3, restoring `mmio_disable_test_mode` for the aarch64 Limine kernel.
Sibling: `co_compiled_duplicate_signature_dispatch_class_2026-08-31.md` — that one is about
duplicates with DIFFERING signatures, which at least warn. This one is identical signatures,
which produce no diagnostic at all.

## Symptom

`src/os/kernel/boot/mmio.spl` and `src/os/kernel/boot/mmio_hardware.spl` both define public
`mmio_read8/16/32/64` and `mmio_write8/16/32/64` with identical signatures. `mmio.spl`'s versions
consult an in-memory test journal when test mode is on; `mmio_hardware.spl`'s go straight to
`rt_volatile_*`, i.e. a raw physical write.

A spec that imports ONLY `os.kernel.boot.mmio`, turns test mode on, and writes, dies:

```
use std.spec.*
use os.kernel.boot.mmio.{mmio_reset_for_test, mmio_test_mode_enabled, mmio_write8, mmio_read8}

describe "probe":
    it "rw":
        mmio_reset_for_test()
        print "mode={mmio_test_mode_enabled()}"    # prints: mode=true
        mmio_write8(0x1000, 7u8)                   # SIGSEGV here
```

```
probe
mode=true
rc=139   (bin/simple run; the test runner reports reason=child-died-by-signal, exit 5)
```

`mode=true` is printed by the same module the write is imported from, so the journal path is the
one the source selects. The write still went to physical address 0x1000 — the call bound to
`mmio_hardware`'s `mmio_write8`.

## What makes it fire

- Reproduces on `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, 2026-09-06).
- Only in a file that does `use std.spec.*`. The identical sequence in a plain `fn main()`, and
  even inside a closure called from `main`, resolves correctly and prints `c 7`. The larger the
  co-compiled module set, the likelier the wrong bind — consistent with the "falling back to the
  last definition" behaviour the sibling record documents.
- No warning is emitted, unlike the differing-signature case.

## Impact

Any module-private helper name that another module also defines can be silently redirected. Here
the redirect turns a test-mode write into a raw MMIO write, which on a hosted process is a SIGSEGV
and on hardware would be a real store to a device address.

## Workaround in place (not a fix)

`src/os/kernel/boot/mmio.spl` calls the `rt_mmio_*` externs directly instead of routing through
`mmio_hardware`'s same-named wrappers, so no collision exists on that path. The collision itself is
untouched: `mmio_hardware.spl` still exports the same eight names, and eight other modules import
them.

## Required fix

Resolve an imported name to the module it was imported FROM, for identical signatures as well as
differing ones, and diagnose an unresolvable collision instead of picking one.
