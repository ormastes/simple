# Windows CPUID C aggregate is not a Simple tuple

Status: C runtime, Rust runtime unit, and narrow-owner Cranelift native execution passed. Canonical-import pure compiler validation and full bootstrap qualification remain pending.

The LLVM-produced compiler crashes in capability detection when optimizing a Cranelift target. The captured native frame is rt_cpuid in the pinned bootstrap runtime archive. Its caller passes ECX=1 and EDX=0, treating the result as a tuple handle. The Windows callee expects RCX to be a writable 16-byte return buffer and leaf/subleaf in EDX/R8D. Its first result store therefore dereferences address 1.

The runtime's existing rt_cpuid returns a four-i32 C struct. Declaring that function as returning a Simple tuple does not describe the same ABI. The fix retains the raw C API and adds rt_cpuid_tuple, which performs one real CPUID query and boxes the four signed register values into the runtime tuple representation. Both C and bootstrap Rust runtimes implement the scalar-handle ABI; the interpreter routes it to its existing tuple-producing handler. The narrow no-GC synchronous SFFI CPU module owns the extern. Compiler capability detection imports that owner, and the host facade re-exports cpuid to preserve its API.

Importing the broad host facade in the first candidate pulled privileged hardware, debugger, TLS and other platform wrappers into the Windows link. The narrow CPU owner avoids that unrelated dependency closure. The failed broad-host objects and link logs are preserved; no missing-symbol stubs were introduced.

No CPU feature or OS-state check is removed. Tuple allocation failure remains nil; no capability bits are manufactured. The new native fixture verifies vendor registers and the x86-64 SSE2 baseline, with zero registers on non-x86 hosts. The Rust unit test compares all four vendor-leaf registers with the raw runtime API.

MSVC-mode C syntax validation passes. The standalone core-C runtime and `rt_cpuid_tuple_selfcheck.c` compiled successfully (39 objects, 40 build jobs); the linked executable passed, comparing all four signed registers for the vendor and extended maximum leaves through real tuple allocation/access. Evidence: C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/cpuid-core-runtime/result.json.

The Rust `test_cpuid_tuple_preserves_registers` regression passed (1 test, 0 failures). The exact CPU owner compiled with Cranelift through a local-import fixture (2 modules, 40 jobs), linked with the real core-C runtime, and ran with exit 0 and `PASS narrow CPUID tuple`. Evidence: `cranelift-tagging-investigation/narrow-cpuid-evidence.json` in the same packet. This local-import result does not prove the canonical `std` routing. A separate pure-compiler canonical-import probe and both repaired compiler builds are still running; full bootstrap and promotion are unproven.

Debug evidence is in C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/pr2385-validation/cranelift-optimizer-crash. Inline assembly was considered but not adopted because the existing asm-template binding bug would not establish correct register outputs.
