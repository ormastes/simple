# SimpleOS direct-LFB blend-span QEMU gate — 2026-08-12

Status: **IMPLEMENTED / BOOT EVIDENCE BLOCKED**.

The x86_64 freestanding runtime now owns `rt_gui_blend_span8`, validates the
tagged source array and row bounds, and performs exact straight-alpha src-over
directly against the registered LFB. `FramebufferDriver` uses it only for an
oversized non-staged MMIO surface and falls back to portable per-pixel blending
when an architecture returns zero. Host-backed and staged surfaces continue to
use `rt_engine2d_simd_blend_span_u32`.

Focused hosted/interpreter parity passes. The canonical readiness command:

`sh scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs`

reports `skip`: QEMU q35/std-vga argument parsing succeeds, but
`SIMPLEOS_KERNEL_ELF` is unset/missing. Therefore no kernel, Direct-LFB call,
QMP screenshot, checksum, or 8K timing has been observed. A future evidence
run must provide a freshly built kernel ELF, reach the desktop serial marker,
capture scanout, and publish viewport/backend/revision/readback/p50/p95/RSS/
fallback/checksum fields. Static disassembly is not sufficient.

## 2026-08-17 re-verification — objdump claim WRONG, a real regex defect found and FIXED

The "GNU `objdump` doesn't support `--disassemble-symbols`" note above is
incorrect as written: `scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs:9`
defaults to `OBJDUMP:-llvm-objdump`, and llvm-objdump supports that option.
Both `--disassemble-symbols` invocations succeed here (traced with `sh -x`).

The script DID fail (exit 1), for a different, real reason: line 34 asserted
the NEON store with `grep -Eq '[[:space:]]st1[[:space:]]+\\{'`. Inside single
quotes `\\{` is a literal backslash then `{` — a malformed ERE repeat. It can
never match the actual disassembly `st1\t{ v0.4s }, [x0]`:

```
ugrep: error: error at position 33
(?m)[[:space:]]st1[[:space:]]+\\{
               invalid repeat___/
old=2   (never matched)
new=0   (matches after fixing to \{)
```

So the NEON-store half of this static gate was **never actually asserting**,
and `set -eu` turned it into a blanket failure of the whole gate. Fixed to
`\{`. The gate now reports:

`PASS: ARM64 NEON and x86_64 SSE2 fill kernels plus receipt symbols` (exit 0)

The boot-evidence blocker above is UNCHANGED and still open: this is a static
prerequisite gate only; no kernel ELF, QMP screenshot, checksum, or 8K timing
has been observed. Spec-test note: this defect lives in a `.shs` host gate that
shells out to clang/llvm-objdump on cross-target objects, so it is not
expressible as an SSpec `.spl` example; the gate script itself is the
regression test and it is now genuinely red-to-green.

## Triage 2026-09-13

Implementation landed per the record; remaining blocker is QEMU boot
evidence requiring a freshly built SimpleOS kernel ELF and a real
serial/QMP screenshot capture. No kernel build or QEMU environment
available/attempted in this lane. Leaving OPEN.

## Recheck 2026-09-22 — x86 direct path absent at e0dd873

The earlier claim that the x86 freestanding runtime owns the direct-LFB
implementation is contradicted by this base revision: `baremetal_stubs.c`
contains no `rt_gui_blend_span4`, while `freestanding_optional_backends.c`
defines it as an unconditional zero-return fallback. Thus an oversized
non-staged x86 surface always takes the portable per-pixel path. The existing
route SSpec expected the missing C body, and the static SIMD gate checked
fill only.

This lane adds the bounded x86 source-over routine, removes the duplicate
fallback symbol, and extends the static prerequisite gate to require its
compiled symbol. The routine rejects invalid source arrays, offsets, counts,
or framebuffer bounds before writing and returns success only after the row.
The host/staged SIMD routes and unsupported-architecture fallbacks are intact.

The x86 C registry currently comes from `rt_gui_set_fb`, which programs BGA
height 768 and stores its own detected framebuffer address and pitch. The
driver can construct a scanout from independent address/height/pitch metadata.
The old four-argument blend ABI did not carry destination identity and could
therefore return success after writing registry A when the requesting driver
owned scanout B. The replacement `rt_gui_blend_span8` carries the
`FramebufferDriver` address, width, height, and pitch and rejects any mismatch
before MMIO access.
`simpleos_direct_lfb_blend_contract_test.c` reproduces the two-buffer mismatch
and proves zero reads/writes on rejection. It also proves transparent pixels
perform zero destination accesses and opaque pixels avoid the old unnecessary
read. The live gate still must establish readback; this is not general 8K
acceleration evidence.

Verification remains blocked before QEMU: the base ARM64 and x86 C translation
units fail to compile for unrelated existing declarations/layout mismatches
(including ARM64 nonce/array fields and x86 `HeapHeader.gc_flags`). The gate
does not report PASS. No guest boot, direct route receipt, readback/checksum,
or 8K timing is claimed. Status remains **OPEN** pending base compile repair,
review, and a fresh guest evidence run.

TODO(deferred-qemu): after a fresh SimpleOS image is available, run the direct
route in QEMU with correlated serial and framebuffer readback, then measure an
8K-width row workload. This host contract test proves bounded arithmetic and
access behavior only; it is not guest, presentation, or 8K performance proof.
