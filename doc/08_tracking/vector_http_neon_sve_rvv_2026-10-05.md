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

## SVE2-required HTTP admission, 2026-10-08

Base fa808ddd63acba540dd01e1819ef3df9e713fb51. The new optional
`--sve2-only` runner mode compiles the unchanged SVE HTTP/bitmap owners with
`-march=armv8-a+sve2` and the baseline provider with
`SIMPLE_VECTOR_REQUIRE_SVE2`. Default mode preserves the existing nine rows and adds these two new rows.
The new mode needs only the installed AArch64 toolchain/sysroot/QEMU.
Selected bitmap kernel sources are included in source.sha256 alongside HTTP.

Actual same-artifact execution:

| CPU | Cases | HTTP vector loops | Bitmap supported | Peak RSS KiB | Exit |
|---|---:|---:|---:|---:|---:|
| max,sve-max-vq=2 |576|1371|1|8380|0|
| neoverse-v1 (SVE without SVE2) |576|0|0|8244|0|

Both receipts report quiescent1 and enforced524288KiB/60s bounds. Execution
was pinned to one allowed host CPU. The existing real dlopen harness checks
byte/CRLF scalar parity, guarded pages, input preservation, capability/error
responses and bitmap admission. ISA inspection found scalable HTTP loads and
first-hit predicate logic; baseline guard disassembly has no scalable vector
instructions. These results prove SVE2-required admission and pre-kernel
refusal on SVE-only, not SVE2-exclusive instructions, Simple cross-app calls,
physical ARM performance or production package authentication.

Artifacts and compile commands: `/var/tmp/item5-http-sve2-admission-20261008/`.
Provider SHA256 afcf321ca1ffe20ecc567acda7f18aa90de159f5abfb477a502fc32c24151eb8;
harness257dc9ca83921e16a72f2d7d34561294d05139a09c0e03fa8a2363d8be540f24.
Final logs/receipts: `/var/tmp/item5-http-sve2-admission-20261008-cycle2/`.
Initial compilation succeeded, but the outer build watchdog caused both inner
new-session guards to reject inherited session contracts (exit89, root_pid0).
Those failures remain retained. A standalone per-row guarded continuation
verified source/artifact hashes and ran only the two previously unexecuted
rows; no recompilation or existing green matrix was repeated. Continuation:
`build/review/item5-http-sve2-execute-20261008.sh`; metrics retained in
`build/review/item5-http-sve2-metrics-20261008.json`.

Reproduction for a fresh output, directly under a normal shell (the runner
owns per-row watchdogs):
`sh scripts/check/check-vector-http-targets.shs /var/tmp/FRESH --sve2-only`.
No provider/kernel implementation or wire ABI changed.
The refused row does load the DSO and query its capability descriptor. Harness
lines33-44 require dlopen/dlsym/query success; lines67-80 call both HTTP opcodes,
assert typed status5 (FEATURE_UNAVAILABLE), zero writes/result -1 and zero
executed kernel iterations. It is a tested provider refusal, not a skipped row.

## Current provider identity rerun, 2026-11-07

Source `205e53cf6571b371fb66631dd59abcb422ee4b26`, merged as `41d9151614adbaadb098b871894537e90593a70f`. This additive evidence preserves all historical findings and remaining acceptance gaps above. The current provider implementation identity includes the directly consumed `text_kernel_private.h`; source implementation and target flags were unchanged.

The canonical http source/build steps succeeded. The first target-launch phase failed with exit 89 and `root_pid=0`: private sparse materialization omitted `scripts/bootstrap/bootstrap-session-exec.c`, required by the watchdog. This was an orchestration dependency failure before any target ran. The original `results.attempt1.tsv` preserves all eleven exit-89 rows. Ten original per-case log/receipt pairs remain as `*.attempt1.*`; the first NEON pair was overwritten because continuation treated the headerless results table as if it had a header. Its original exit 89 remains recorded in the table. After adding the exact tracked source helper, only the canonical previously unexecuted run sections were replayed. All existing target object, DSO and harness hashes were sealed before continuation and verified unchanged afterward; successful compilation was not repeated.

All 11 rows below exited 0 with `quiescent=1` and no unexpected session PIDs. Each used the canonical 60-second/524288 KiB enforced watchdog. The continuation coordinator also terminated normally.

| Case | HTTP cases | HTTP vector iterations | Bitmap supported | Peak RSS KiB | Exit |
|---|---:|---:|---:|---:|---:|
| neon | 576 | 2247 | 1 | 9124 | 0 |
| neon-no-http | 576 | 0 | 1 | 9040 | 0 |
| sve-1 | 576 | 2535 | 1 | 8812 | 0 |
| sve-2 | 576 | 1371 | 1 | 9120 | 0 |
| sve-4 | 576 | 819 | 1 | 9060 | 0 |
| no-sve | 576 | 0 | 0 | 9048 | 0 |
| rvv128 | 576 | 2535 | 1 | 9052 | 0 |
| rvv256 | 576 | 1371 | 1 | 8904 | 0 |
| no-v | 576 | 0 | 0 | 8984 | 0 |
| sve2-enabled | 576 | 1371 | 1 | 9032 | 0 |
| sve2-sve-only-refused | 576 | 0 | 0 | 9016 | 0 |

Exact current target artifact SHA256 values:

| Artifact (relative to evidence root) | SHA256 |
|---|---|
| `http/neon/check` | `257dc9ca83921e16a72f2d7d34561294d05139a09c0e03fa8a2363d8be540f24` |
| `http/neon/forced.so` | `523c053fcfe9981b18ee84f5ebf9ba644ca75108a76c91f4aa8d8a00dc16f0c0` |
| `http/neon/provider.so` | `9d72f59fb61c2287923d54860e062b0c20a400d6e60248fbd88164e202ddd46f` |
| `http/rvv/check` | `5eb800d19023e4d80e69da63863f8f6088dbfbea989fa1f3ac21b64cd0f87a15` |
| `http/rvv/provider.so` | `bde8931c82ae5b46087c51e23d7ef3fdd3ed0c03a3f43cf671d6d0083fe7aad8` |
| `http/sve/check` | `257dc9ca83921e16a72f2d7d34561294d05139a09c0e03fa8a2363d8be540f24` |
| `http/sve/provider.so` | `7638eef514fcf57eb3d5f36562fa66083a73e7621ec0c31e8e34d5c0de79a71d` |
| `http/sve2/check` | `257dc9ca83921e16a72f2d7d34561294d05139a09c0e03fa8a2363d8be540f24` |
| `http/sve2/provider.so` | `32204d02e4b6e9e25b8f2d3cbe824b0994c7ce968c19490731f84464872d2fa3` |

Provider ELF targets are AArch64 (machine 183) and RISC-V (machine 243). Bitmap constructor-observer DSOs remain diagnostic artifacts; their loader/lifetime evidence is not transferred to a production Simple application. HTTP rows exercise the canonical C guard-page, input-preservation, output and refusal oracles.

Tool identities (Clang/LLVM 23.1.3, QEMU 10.2.1 and GNU ld 2.46):

| Tool | SHA256 |
|---|---|
| `/usr/lib/llvm-23/bin/clang` | `c300fb439c33a9b2cbde6112a09681ce8278a5bb08bdea3ba0cc91e32d07120d` |
| `/usr/lib/llvm-23/bin/llvm-objdump` | `9671832fd326a5fd6f923e583b5f23b854984864d50c0b26a7647b976f9c4d0a` |
| `/usr/bin/qemu-aarch64` | `e1dc1eb07f2c205a22ac489240578d14d396d767a35bb3734a5ef12f1848ed20` |
| `/usr/bin/qemu-riscv64` | `7a61faa44933bd2d3830f32cd93b98663267ea4b8fe669daea871c398273b7ef` |
| `/usr/bin/aarch64-linux-gnu-ld` | `ef1f32f9d5f522ae9721fe0de846c10fa1ca04f859d491ab30541e9f925b9408` |
| `/usr/bin/riscv64-linux-gnu-ld` | `2bb1314b49f90406e558cfc9d4e28776601617c4c05bd9673117c663b79e3f18` |

Target runtime files (hosted target libc/loader, not a Simple runtime archive):

| File | SHA256 |
|---|---|
| `/usr/aarch64-linux-gnu/lib/ld-linux-aarch64.so.1` | `de9354274cf75ec36e280d3a1a072c4c5736bfb77299b1dba8a10c9ea6efbd3b` |
| `/usr/aarch64-linux-gnu/lib/libc.so.6` | `8f2c2a16a4ee3d5a6e37d1a793ad59f0dfd7dcd216063d230a23e58744dae7ea` |
| `/usr/riscv64-linux-gnu/lib/ld-linux-riscv64-lp64d.so.1` | `d6976785d56eafc476d2e8de278373e397641024c47b48206222dbf36be1da02` |
| `/usr/riscv64-linux-gnu/lib/libc.so.6` | `8d64ca7f710285795d072a9073451d949bff472903562897cfabee6aeaf06292` |

Source and evidence bindings:

- Complete tracked source inventory `source-identity.json`: `8dbbc60bf8325cc20199d1c85d70f5b0a84418bc6a488d74057b4db5785dfb11`.
- Canonical script `scripts/check/check-vector-http-targets.shs`: `87d4392801366682df5ae36e7578d9299e838f9b224df63151a8f65ffa209551`.
- ABI header: `a36697d78898a885daefa440b879207ba6e0dd8215b62eb2585bb10650f3578f`.
- Direct text header: `bd2760581182ac03e89bb351335a2743c1d0dab53f802f655af5501f9388757d`.
- Full result/artifact ledger `qualification-summary.json`: `9dc23c6d0d237a1f1ce221a8cde20eb9c6fd62a8c17d3aac81b00b5ecfe82910`.
- Tool/runtime ledger `tool-runtime-identities.json`: `61fc697348b7d0ac24c333af5b4d8dfee5e132fb827f266c10ff3cb67d693e9c`.
- Continuation receipt `http-continuation-terminal.json`: `cba2024ad517bb1a7f3cc8f07843fd1aeb53ca05e51d93b51d1268c5ba92b7cf`.

Durable evidence root: `D:/dev/simple/build/review/item5-cross-canonical-205-20261107/` (WSL `/mnt/d/dev/simple/build/review/item5-cross-canonical-205-20261107/`). Exact row outputs and per-case watchdog receipts are under `http/`; original prelaunch exit-89 records remain adjacent. The continuation terminal binds the replayed canonical run-section hash and unchanged target artifact hashes. No six-profile identity regression or already successful C build was rerun for this documentation.

**Scope:** real target C component execution and dynamic loading under QEMU. This does not qualify Simple DB/HTTP binaries, native hardware performance, full Phase3, aspects/log/profile/AOP, CUDA/device execution, or deployed production provider packaging. The SVE2-labeled build uses SVE kernels and does not establish execution of an SVE2-only opcode. Existing bitmap input-preservation/scalar-result-sentinel coverage limitations remain open.
