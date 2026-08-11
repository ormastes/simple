# BUG: rt_extras.c RuntimeString layout 4 bytes off vs baremetal_stubs.c — string-data reads shifted

**Status:** RESOLVED (2026-07-12)
**Severity:** medium-high (every rt_extras.c string-data read returns bytes shifted 4 early; silent corruption)
**Component:** SimpleOS x86_64 freestanding runtime — `examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c` vs `boot/baremetal_stubs.c`
**Found:** 2026-07-11 (clang file-launch lane; explains `rt_text_to_bytes` elements reading as zeros)

## Symptom

`rt_extras.c` declares/assumes a RuntimeString struct layout that is 4 bytes
smaller/offset than the layout `baremetal_stubs.c` (and the Simple compiler's
emitted objects) actually use. All string-data accesses in rt_extras.c read 4
bytes early: `rt_text_to_bytes` returned zero elements for valid text, and
argv marshalling via that path produced garbage.

## Workaround in place

argv bytes for ring-3 exec are now copied by `rt_text_copy_to_phys`
(baremetal_stubs.c, C-dump-verified byte-perfect: `99 108 97 110 103 0 ...`).
rt_extras.c itself still has the wrong layout.

## Fix direction

Single source of truth for the RuntimeString C layout (shared header included
by both rt_extras.c and baremetal_stubs.c), then re-verify rt_text_to_bytes
returns correct bytes in-guest. Audit other rt_extras.c accessors for the same
shift.

## Resolution (2026-07-12)

Root cause was the SHARED header, not rt_extras.c itself:
`arch/common/baremetal_runtime.h` declared `RuntimeString.len` as `uint32_t`
(data[] at offset 12) while the compiler emits `u64 len` (data at offset 16) —
every string-data read in every header includer was 4 bytes early. Fixed to
`uint64_t` with `_Static_assert(offsetof(len)==8 / offsetof(data)==16)` in both
the header and baremetal_stubs.c to lock the contract.

Includer audit: rt_extras.c (10 accessors healed), primitives.c (13 accessors
healed — string_char_at, substring, parse_int, spl_str_to_cstr, glob_matches
etc. were all silently shifted), collections.c / hashmap.c /
baremetal_boot_stdout.c (zero string accesses, unaffected).

Verified in-guest: rt_text_to_bytes probe prints expected==actual bytes
(83 73 77 80 76 69, len 6) — probe entry landed at
`examples/09_embedded/simple_os/arch/x86_64/rt_text_bytes_probe_entry.spl`;
ssh_clang_hello_ring3 + ssh_multi_cmd gates both green on the fixed kernel;
objdump shows len reads at +0x8, data at +0x10.

Pre-existing, NOT covered here (flagged during audit): (1) rt_text_to_bytes
returns a tagged RuntimeValue array while [u8] callers expect BYTE_PACKED —
latent encoding mismatch; (2) header RuntimeArray (u32/inline) vs
baremetal_stubs.c RuntimeArray (u64/pointer) divergence.
