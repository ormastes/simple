# HTTP byte/CRLF provider kernels: NEON, SVE and RVV

Base: `29d73eb8d34e5af07f2cab174cd81ee524fa8ad5`. This extends the existing
native provider slice, not the Simple HTTP server or compiler. The 64/24-byte
wire, opcode 3/4, capability 4/8 and ABI digest are unchanged. Borrowed byte
input is synchronous; successful searches return zero bytes_written and the
first relative index or -1. Empty spans, malformed arguments, unused spans
and capability refusal use the existing contract.

## Source design

`SIMPLE_VECTOR_ENABLE_HTTP` is an explicit build option. The original x86
`SIMPLE_VECTOR_ENABLE_HTTP_AVX512` remains a supported alias; default images
retain bitmap-only capability bits and no HTTP symbol dependency. The x86
AVX512F/BW and XSTATE admission code is preserved. AArch64 HTTP calls use the
selected image's existing ASIMD/SVE/SVE2 admission; RISC-V uses its V HWCAP.
Optional instructions remain in separate kernel translation units.

- `http_neon.c`: 16 candidate bytes; CRLF requires 17 input bytes before the
  shifted LF load. First matching lane is selected in order, followed by a
  bounded scalar tail.
- `http_sve.c`: predication bounds the candidate starts. For CRLF there are
  `max(bytes-1,0)` candidates, so both loads stay inside the input even in the
  final partial vector. Break-before predicate count yields the first index.
- `http_rvv.c`: the same candidate bound sets e8m1 vl; comparisons and vfirst
  find the first match. A zero vl refuses execution instead of looping.

No kernel retains pointers, modifies input or exposes target vectors across
the C ABI. The existing shared selfcheck now accepts explicit cross-target
CPU expectations; its original x86 feature detection and forced-BW mode remain.

## Actual QEMU execution, 2026-10-05

```sh
sh scripts/check/check-vector-http-targets.shs \
    /var/tmp/item5-http-vector-targets-20261005
```

Every row executed a real cross-compiled harness and dlopened provider. Each
row passed 576 scalar-differential or refusal cases, plus malformed request,
capability, input-preservation, response-canary and small bitmap checks.

| Target/profile | HTTP vector iterations | Bitmap result | Exit |
|---|---:|---|---:|
| NEON / max | 2247 | executes | 0 |
| NEON / forced HTTP unavailable | 0 | executes | 0 |
| SVE / max, 128-bit VL | 2535 | executes | 0 |
| SVE / max, 256-bit VL | 1371 | executes | 0 |
| SVE / max, 512-bit VL | 819 | executes | 0 |
| SVE image / cortex-a53 | 0 | refuses | 0 |
| RVV / rva23u64, VLEN128 | 2535 | executes | 0 |
| RVV / rva23u64, VLEN256 | 1371 | executes | 0 |
| RVV image / max,v=false | 0 | refuses | 0 |

Lengths 0..257 include vector boundaries, final partial lanes, high-byte and
NUL searches, lone final CR, CRLF at 63/64 and 127/128, and offset spans.
Inputs ending at a PROT_NONE page detect overreads. Real loop counters and
kernel disassembly establish executed vector kernels rather than scalar-only
replacement implementations. Baseline disassembly excludes scalable/vector
instructions for the SVE/RVV dispatch owners. Each row used an enforced
524288 KiB RSS / 60-second process-tree watchdog.

Retained evidence directory contains per-row logs/receipts, results.tsv,
toolchain and sysroot identities, source SHA-256 manifest, per-image artifact
hashes, provider identities and disassembly. Separate compilation-only checks
confirmed the old x86 macro still links the HTTP owner, while the default
provider has no HTTP undefined symbol (`x86-compat.log`). No unchanged x86
native criteria or full bitmap matrix was rerun. Diff and shell syntax checks
passed; release gates are separate from this evidence.

## Limits

QEMU correctness is not physical ARM/RISC-V execution or performance. SVE2-only
instructions are not implemented or newly qualified here. The forced NEON
HTTP refusal tests dispatch policy, not a physical AArch64 CPU without ASIMD.
No Simple application, loader-session integration, end-to-end HTTP request,
speedup, host-registry authentication or device-image attestation is claimed.
No root Simple job, compiler freeze or shared cache was modified. The check is
registered as an explicit toolchain/emulator lane, not a generic CI pass.
