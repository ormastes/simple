# SimpleOS direct-LFB blend-span QEMU gate — 2026-08-12

Status: **IMPLEMENTED / BOOT EVIDENCE BLOCKED**.

The x86_64 freestanding runtime now owns `rt_gui_blend_span4`, validates the
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
