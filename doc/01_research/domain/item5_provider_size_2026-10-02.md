<!-- codex-research -->
# Item 5 domain research: trustworthy demand loading and size evidence

## 2026-10-11 primary-source variation update (Astra)

The [independent review](../local/item5_variation_astra_review_2026-10-11.md) extends the selected proposal with these source-backed constraints. This is domain research, not a measurement or support claim.

- ISA legality differs from width and tuning. Preserve exact registered feature requirements and target-independent semantics. [GCC x86 options](https://gcc.gnu.org/onlinedocs/gcc-15.1.0/gcc/x86-Options.html).
- SVE state/vector length is per thread; fixed-VL code needs a qualified worker domain. [Linux SVE](https://www.kernel.org/doc/html/latest/arch/arm64/sve.html). RISC-V vector enablement is separately controlled for the calling thread. [Linux RISC-V vector interface](https://docs.kernel.org/arch/riscv/vector.html).
- Hardware presence alone does not grant dynamic extended-state permission. [Linux XSTATE](https://docs.kernel.org/arch/x86/xstate.html). RVV tail-agnostic lanes must not be assumed zero; distinguish VLEN, active VL, SEW and LMUL. [RISC-V vector specification](https://docs.riscv.org/reference/isa/extensions/vector/_attachments/riscv-v-spec.pdf).
- Shared vectorization legality can support distinct loop/SLP matching and target profitability. [LLVM vectorizers](https://llvm.org/docs/Vectorizers.html).
- CUDA submission may precede device completion; retain resources to the actual dependency/completion boundary. [CUDA asynchronous execution](https://docs.nvidia.com/cuda/cuda-programming-guide/02-basics/asynchronous-execution.html).
- Execution completion and memory visibility are separate Vulkan obligations; noncoherent memory needs the API's actual visibility handling. [Vulkan synchronization](https://docs.vulkan.org/spec/latest/chapters/synchronization.html), [Vulkan memory](https://docs.vulkan.org/spec/latest/chapters/memory.html).

These constraints add structural and failure/lifetime tests, not invented numerical budgets. Preserve NFR-001..007 and require actual matched app/target evidence before claiming speed or availability.

Date: 2026-10-02. Scope is the full retained kernel/extension aspect dynload
and binary-size contract, including all supported targets. These findings
extend existing research without changing user-selected requirements.

## Link closure is observable output, not a flag claim

GNU ld documents `--as-needed` as sensitive to whether a library satisfies
an unresolved reference at that point in the command line. Section garbage
collection starts from entry/undefined roots and sections referenced by
dynamic objects. Consequently enabling GC/as-needed cannot establish exclusion
alone: inspect produced sections, symbols, archive members and dynamic
dependencies, retaining link order and map evidence. Hidden symbols and
explicit export roots require review because visibility changes retention.

Source: [GNU ld options](https://sourceware.org/binutils/docs/ld/Options.html).

Design consequence: independently parse the produced dependency inventory and
root reasons. Mutate a root or inject a provider dependency and require the
evidence gate to fail. Test the production link path, not requirements tokens.

## Loader lifecycle requires owned sessions

Linux dynamic loading uses reference-counted handles; local symbol visibility
does not provide a permanent isolation boundary because a local object can
be promoted through later loading dependencies. Successful close need not
immediately remove mappings. Providers therefore need explicit pin ownership,
callable-symbol checks, and refusal after session close; loader return values
cannot replace those invariants.

Sources: [Linux dlopen](https://www.man7.org/linux/man-pages/man3/dlopen.3.html),
[POSIX dlclose](https://www.man7.org/linux/man-pages/man3/dlclose.3p.html).

Design consequence: before demand, assert independently observed map/init
absence. During use assert exact admitted identity and single-flight
activation. Lifetime acceptance verifies pin refusal and stale-call rejection;
it does not claim immediate native unmapping. Test constructors/effects so
rejection before execution is observable rather than inferred from metadata.

## Architecture and measurement constraints

Linux ELF receipts cannot certify Windows PE, Mach-O, BSD or bare-metal
behavior. Target capability manifests must identify supported behavior and
typed refusal separately; unavailable target runs remain incomplete.
Kernel/driver layers use the repository's MDSOC-only routing.

Retain real compiler/source/artifact/linker/profile identities. Match startup
wrapper, core archive, flags and strip policy for the selected C comparator;
its entry prints identical bytes via `puts`. NoGC and provider/init exclusion
need independent traces. Use >=30 development or >=100 release samples and
report p50/p95 and max RSS against the same-host Python baseline. A synthetic
receipt may test checker rejection but never qualifies production performance.

Admission must bind immutable artifact digest, ABI, dependency closure,
capability/policy, target and architecture before effects; installed compiled
provider artifacts must be atomic and support rollback. Command capsules do
not replace in-process extension correctness or independently loadable sealed
pure-Simple provider sections. Pure-Simple promotion needs failure/resource/
performance/architecture parity; effectful dual mode executes once.
