# MC/DC Aspect Object Converter Evidence — 2026-08-22

Scope: the isolated x86_64 C aspect provider object and its pre-SMF admission
oracle. This is cold build-time evidence, not dynamic-patchpoint latency and not
an executed pure-Simple conversion claim.

Command:

```text
scripts/check/check-mcdc-aspect-object-converter.shs
```

Observed on the current Linux x86_64 host:

```text
PASS object_bytes=1200 iterations=10000 mean_ns=410 maxrss_kib=1792 heap_allocations=0
PASS reproducible_object_sha256=707026d886e0a16d4f4558e35b177b287a85c91d7a862600849760e8a173e20b static_off_build_calls=0
```

The same oracle compiled with GCC AddressSanitizer plus UndefinedBehaviorSanitizer
also passed all 10,000 iterations (`1,507 ns` mean, `6,912 KiB` instrumented
max RSS). No sanitizer diagnostic was emitted.

The oracle uses one fixed 1 MiB object buffer and performs no heap allocation.
Production conversion rejects objects above 1 MiB, more than 64 sections,
symbols, or relocations, and vector code above 64 KiB. It copies only the two
admitted symbol extents into the relocation-capable SMF writer. Static-off
branches before parsing, hashing, conversion, or SMFAPK construction.

The two independently compiled objects were byte-identical. The compiler flags
disable unwind tables, stack-protector material, and control-flow note sections,
leaving exactly one immutable executable section and one immutable non-executable
marker section. The converter rejects writable executable material, additional
allocated sections, implicit imports, and relocation kinds unsupported by the
current loader.
