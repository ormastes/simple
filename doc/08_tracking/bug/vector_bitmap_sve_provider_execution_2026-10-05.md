# SVE bitmap provider execution and SVE2 feature admission

Scope: native C provider AND/OR over raw u32 spans, unchanged SIMDKER1
64-byte request/24-byte response and interface digest. Not a Phase2/Simple
application result, full ARM completion, or hardware performance claim.

Baseline `bitmap_provider.c` retains NEON as the default AArch64 selection.
Explicit SIMPLE_VECTOR_REQUIRE_SVE selects HWCAP_SVE; REQUIRE_SVE2 selects
HWCAP_SVE and HWCAP2_SVE2. Both macros together fail compilation. The baseline
TU uses armv8-a plus general-registers-only, separate from scalable code.
Borrowed span validation, overlap refusal and handle/capability rules remain
unchanged; the provider retains no borrowed pointers beyond each call.

`bitmap_sve.c` uses whilelt predicates, predicated loads/stores and natural
AND/OR. The final partial vector accesses active words only; svcntw determines
the step. Separate SVE and SVE2-required shared artifacts have distinct
provider and implementation identities. Both kernels use SVE instructions:
requiring/compiling SVE2 does NOT prove a SVE2-exclusive instruction executed.
Future meaningful SVE2-specific work should consider existing byte-find/CRLF
wire operations3/4, not insert artificial instructions into bitmap operations.

Arm's [SVE2 introduction](https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/102340_0001_02_en_introduction-to-sve2.pdf?revision=b208e56b-6569-4ae2-b6f3-cd7d5d1ecac3)
describes predicate-controlled active lanes; the retained emitted disassembly
and scalar oracle below are the evidence for this implementation.

## Actual native evidence

Base eff05db338d813ca93a39cfdd9b23dde988d90b1. Clang23/QEMU10.2.1,
installed AArch64 libc development sysroot. Binaries compiled once; execution
used the same two artifact sets. Each row passed70357 harness checks:

| Artifact | QEMU CPU | Vector iterations | Peak RSS KiB |
|---|---|---:|---:|
| SVE | max,sve-max-vq=1 (128bit) |3636|8508|
| SVE | max,sve-max-vq=2 (256bit) |1832|8452|
| SVE | max,sve-max-vq=4 (512bit) |932|8164|
| SVE2-required | max,sve-max-vq=1 |3636|8312|
| SVE2-required | max,sve-max-vq=2 |1832|8236|
| SVE2-required | max,sve-max-vq=4 |932|8520|
| SVE | cortex-a53, no SVE |0|8260|
| SVE2-required | cortex-a53, no SVE |0|8504|
| SVE | neoverse-v1, SVE without SVE2 |1832|8148|
| SVE2-required | neoverse-v1, SVE without SVE2 |0|8520|

Every row completed exit0, quiescent1 under60s/524288KiB enforce watchdog.
Expected iteration counts derive from the harness's17 lengths, two offsets
and two opcodes, with ceil(words/lanes) iterations; the runner checks these
counts to detect silently unchanged vector length. Refusal rows require zero
vector iterations and unchanged output. Actual kernel disassembly contains
whilelo, ld1w, and, orr, st1w over scalable registers. Baseline disassembly
contains no scalable vector/predicate register instructions.

Durable evidence: `/var/tmp/item5-sve-bitmap-20261005-r1/`; final VL/no-SVE
logs/receipts use `*-exec1.*`; SVE-only discrimination uses `sve-v1.*` and
`sve2-v1.*`. `results-exec1.tsv` retains the first unsupported CPU-property
attempt as well as successes; `results-v1.tsv` holds the corrected two rows.
Source/toolchain/sysroot hashes and per-family object/disassembly hashes are
retained. Provider SHA256:

- SVE: b160d9f35792616581328d062959bac2a16e3fafd18d706a660ff2a3316e4b6a
- SVE2-required: af5b06b3bb66343219f1f779a981b9667bb03541987126a95aa567e54ab95d5b

Initial execution failed before QEMU admission because the sparse worktree
lacked watchdog session-helper source; exit89 receipts remain. After restoring
that tracked prerequisite, eight rows passed. QEMU rejected `max,sve2=off`
(property unavailable); only those two failed setup rows were rerun with its
existing neoverse-v1 CPU model. No passing native row or compilation was rerun.
The runner now uses that model and checks the watchdog source before building.
Those orchestration edits received syntax/static validation only.

## Limits and reproduction

Run `sh scripts/check/check-vector-bitmap-sve.shs /var/tmp/NEW_FRESH_OUTPUT`
on a host with the documented cross prerequisites. The manual guard exemption
records why ordinary hosted CI cannot execute this target matrix.

Constructor-observer DSOs intentionally depend on a harness export and are
diagnostic artifacts, not deployable packages. Counter reads do not load the
provider. The inherited harness checks scalar output and canaries but does not
snapshot/assert input preservation or assert scalar_result=-1; those remaining
contract checks are not claimed complete. Simple loader pin/session lifetime,
constructor-free packaging, physical hardware timing, SVE2-exclusive operations
and real compiler/app calls remain unqualified. Existing NEON/RVV/AVX evidence
was preserved and not rerun; no new qualification of those rows is inferred.
