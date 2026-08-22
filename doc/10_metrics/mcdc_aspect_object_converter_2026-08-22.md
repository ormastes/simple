# MC/DC Aspect Object Converter Evidence — 2026-08-22

Scope: the isolated x86_64 C aspect provider object, its pre-SMF admission
oracle, and the C runtime surfaces used by retained inner-SMF activation. This
is not an executed pure-Simple conversion or loader claim.

Command:

```text
scripts/check/check-mcdc-aspect-object-converter.shs
```

Observed on the current Linux x86_64 host:

```text
PASS object_bytes=1200 iterations=10000 mean_ns=178 maxrss_kib=1792 heap_allocations=0
PASS smf_relocated_call=1 iterations=1000000 resolve_mean_ns=4 disarmed_mean_ns=15 maxrss_kib=1792 heap_allocations=0 sink=0
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

Activation now parses and validates the retained SMF relocation table before
mapping, resolves only `rt_mcdc_record_compiled_vector_v1` through a dedicated
allocation-free address bridge, checks four-byte patch bounds and signed PLT32
arithmetic, and targets a fixed 13-byte in-mapping absolute import thunk so ASLR
cannot place the runtime outside PLT32 reach. It patches under RW, restores RX,
flushes the instruction cache, and only then registers or binds the target. The
C self-check executes the synthetic retained-SMF call shape through that thunk,
and the checker asserts publication ordering from source. Linker-wrapped
malloc/calloc/realloc evidence observed zero heap
allocations across one million address resolutions and one million disarmed
patchpoint calls. The 15 ns disarmed number is a focused host smoke, not a
cross-host NFR result.

The two independently compiled objects were byte-identical. The compiler flags
disable unwind tables, stack-protector material, and control-flow note sections,
leaving exactly one immutable executable section and one immutable non-executable
marker section. The converter rejects writable executable material, additional
allocated sections, implicit imports, and relocation kinds unsupported by the
current loader.
