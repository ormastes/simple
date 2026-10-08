# GNU public CPU queries retained a libgcc startup constructor

The GNU branches of `rt_simd_has_sse/avx/avx2` referenced compiler CPU
builtins. Linking the otherwise-unused dispatch object extracted libgcc's
`cpuinfo.o`; its constructor survived section collection in a no-demand ELF.

The queries now share a stateless CPUID/XGETBV probe with the GNU AVX2 kernel
detector. Public capability bits remain independent of compiled kernels and
`SIMPLE_RUNTIME_FORCE_NO_AVX2`. XGETBV requires XSAVE, OSXSAVE and AVX;
AVX requires XMM/YMM state, and AVX2 requires leaf 7 availability and EBX5.
MSVC/clang-cl query branches and AVX512 guards remain unchanged. GNU i386
can include CPUID independently of the x86-64 kernel compilation gate.
No new constructor, cache, allocation or mutable once-state was added.

## Actual bounded native evidence

Base: `af44ec6da108fe06325d902780e3a7a74c21acaa`. GCC native C only; no
Simple compiler, Cargo archive, or app rebuild was performed.

Retained directory: `D:/dev/simple/build/review/item5-cpu-query-20261008`.
`run-1.log` passed under a 180-second, 1,048,576-KiB watchdog; peak RSS
164,616 KiB. `resources-1.env` records terminal exit 0 and containment.
The earlier `resources.env` is a prerequisite failure before child launch:
the sparse checkout lacked the tracked session helper; it was materialized.

- Native and forced-kernel-off: public bits 7, matching the separately linked
  builtin oracle. Forced kernel admission was zero while public AVX2 stayed true.
- QEMU Nehalem: public bits 1, matching its separately run builtin oracle.
- Each row checked 1,280 raw feature/leaf/XSTATE combinations and 4,000
  concurrent repeated public queries. This is not a first-use timing claim.
- The unchanged compiler/link flags linked the production dispatch object
  plus a no-query entry point before and after. ELF bytes fell from 19,936
  to 15,600; `size` text/data/bss totals fell from 7,719 to 1,783 bytes.
- Baseline ELF retained `__cpu_indicator_init`; after-object undefined symbols
  and after-ELF symbols contain neither that symbol nor `__cpu_model`.
  Link maps, init-array dumps, compiler version and binary/source hashes are
  retained under `evidence/`. The oracle is never linked into these ELFs.

Reproduce once in a fresh directory using
`scripts/check/check-cpu-query-lazy.shs ABSOLUTE_OUTPUT_DIRECTORY` under the
resource watchdog. `CPU_QUERY_GIT_REPO` may point to the object-owning repository
when a Windows worktree's Git pointer is not readable from WSL.

Limits: no Windows/i386 executable qualification, public-query latency
benchmark, full compiler image measurement or provider/application performance
claim. SSE query now also probes available AVX state, adding direct probe work;
it introduces no startup work. Existing AVX512 execution guards are preserved,
not newly qualified by this check.
