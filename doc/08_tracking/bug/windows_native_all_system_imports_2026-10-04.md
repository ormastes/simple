# Windows native-all system imports omitted at final link

Status: stale producer configuration identified. Both retained-object
diagnostic relinks succeeded, and the real MSVC SDK regression passed. Hello,
subsystem tests, Phase 2 admission and release qualification remain pending.

Both Windows LLVM and Cranelift Phase 2 attempts using source
`9737d1217bc44439b56bba6c2ef16faaff51bd20` reached
`compiled=1175 reused=0 failed=0`, then returned a final-link failure. Sixteen
unresolved imported functions come from the sysinfo dependency retained in
`simple_native_all.lib`:

| Provider | Missing imported functions |
|---|---|
| `pdh` | `PdhAddEnglishCounterA/W`, `PdhCloseQuery`, `PdhCollectQueryData/Ex`, `PdhGetFormattedCounterValue`, `PdhOpenQueryA`, `PdhRemoveCounter` |
| `powrprof` | `CallNtPowerInformation` |
| `netapi32` | `NetApiBufferFree`, `NetGroupEnum`, `NetGroupGetInfo`, `NetUserEnum`, `NetUserGetInfo`, `NetUserGetLocalGroups` |
| `psapi` | `GetModuleFileNameExW` |

The Rust bootstrap compiler's native-project linker selects its system
libraries through `PlatformLinkConfig`. The actual seed was built from
`2aabdc201a0c0e977baf9a9be4b0d89cf6859f88`, whose Windows MSVC and MinGW lists
omit these four providers. In contrast, the target source `9737d1217bc` already
includes the fix in `0abc0fefa78`. Target-source freshness did not update the
running seed's compiled linker policy. An initial proposed duplicate addition
was removed during peer review; no second copy of these libraries is needed.

Apply the existing four-library repair to the new retained-object link. Do not
stub the functions or permit unresolved symbols. This changes bootstrap link
inputs, not runtime ownership, memory management, or API semantics. A later
seed refresh must include the existing linker repair alongside the enum/bool
fixes, rather than selecting a seed lineage which loses it.

Preserve both failed attempts and reuse their completed native objects for a
new owned link attempt. Original nonverbose link commands were not retained;
any reconstruction must be labelled as reconstructed from the exact linker
source and retained inputs. Bind the original source, generated objects,
runtime archives, actual SDK libraries, and repair configuration to the new
artifact. Do not rewrite the failed build receipt to imply success.

The Windows regression must exercise real SDK linking from the production
library configuration and run the resulting probe, without calling the
account or power-management APIs. Check that the same fixture fails with the
actual old producer policy (the four providers omitted). The current target
policy should already pass. A list-membership assertion alone does not prove
symbol resolution. MinGW source coverage is not a claim that a MinGW toolchain
was executed.

The focused regression compiled the sixteen-address C fixture against the
installed x64 MSVC SDK. Its negative used a library-list emitter compiled
from the actual old source's `Target` and `PlatformLinkConfig`, rather than a
handwritten list. That policy failed with the expected missing imports from
all four provider families. The actual current production configuration
linked and the executable returned zero with `sdk-imports=16` and empty
stderr. No account, power, performance-counter or process-image API was
called. The standalone harness included the real common-owner source and
the same Cargo integration-test file; no seed or full frontend was rebuilt.

Bounded evidence is retained in the isolated regression owner's
`build/sdk-import-regression1/validation3.receipt.env`: complete Windows Job,
raw/native zero, 120-second limit, 2 MiB stream bound, 367 actual log bytes,
log SHA256 `f5ce337a67cf73127ceec7e0e961a99bcd0e73a1b2ed32c565889dc6776be818`.
The collector terminated the remaining SDK telemetry helper after the root
exited; its recorded PID 57204 was independently observed absent. Physical
old/current policy hashes, their pinned Git-blob equivalence, unique receipt
keys and actual log byte/SHA checks are recorded in the adjacent
`source-and-terminal-proof.json`. Earlier CMD transport and
SDK-header collision failures remain separate retained evidence. The test is
restricted to Windows x86-64 MSVC; it does not require an MSVC installation
from a Windows GNU Cargo suite.

Local evidence: `windows-restart-20261004/p2-post-bool-refresh/llvm/`
`link-failure-summary.json`; Cranelift has the same terminal failure. Retained
object roots are `C:/dev/native-objects-wZhh40` (LLVM) and
`C:/dev/native-objects-1Y0T6v` (Cranelift). Derived bug-database registration is
pending; this note must not be treated as a completed release qualification.
