# Full Pure-Simple SIMD Bootstrap Requirements

Status: Selected

Selected direction: Option A, complete fixed and scalable cross-target program.
Selected by the user on 2026-09-08.

## Functional requirements

- REQ-SIMD-001: Provide one pure-Simple SIMD API with scalar fallback and explicit runtime capability dispatch.
- REQ-SIMD-002: Implement x86 SSE2, SSSE3, SSE4.1, AVX, AVX2, and AVX-512 paths without executing an unsupported instruction.
- REQ-SIMD-003: Implement Arm NEON, SVE, and SVE2, RISC-V V, and WebAssembly SIMD128 paths. Unavailable native hosts remain visible as blocked rows with exact resume commands and retained emulated evidence.
- REQ-SIMD-004: Preserve scalar semantics for integer overflow, shifts, masks, comparisons, floating-point edge cases, alignment, tails, and aliasing on every backend.
- REQ-SIMD-005: Keep database and web-server callers platform-neutral and select SIMD only behind shared library/compiler interfaces.
- REQ-SIMD-006: Apply measured SIMD kernels to representative database scanning/filtering and HTTP parsing/classification hot paths, retaining scalar fallbacks.
- REQ-SIMD-007: Keep the compiler, interpreter, runtime, libraries, database, web server, MCP, and deployment implementation pure Simple; platform adapters may expose capabilities but may not become product dependencies.
- REQ-SIMD-008: Complete the trusted four-stage bootstrap and bind all verification and deployment receipts to the exact admitted Stage 4 binary. Rust-seed or raw-source execution is not release evidence.
- REQ-SIMD-009: Rebuild and redeploy the Simple CLI, Simple MCP server, and Simple LSP MCP server from admitted cached native artifacts, with rollback evidence.
- REQ-SIMD-010: Verify compiler and interpreter behavior at each admitted bootstrap phase, including all phase-supported unit, integration, system, and doctest suites.
- REQ-SIMD-011: At every admitted phase, verify MCP, Simple LSP MCP, SPipe/SSpec, DevHub, and LLM Caret suites through the exact phase artifact. Unsupported phase operations must fail closed and remain recorded.
- REQ-SIMD-012: Produce a phase matrix containing artifact path, SHA-256, provenance, capability set, command, result, duration, and retained receipt for every compiler/interpreter and tool-suite row.
- REQ-SIMD-013: Update current SIMD research, architecture, detailed design, executable SPipe scenarios, generated manuals, operator guides, and the agent task plan before final verification.
- REQ-SIMD-014: Run the repository release gates once against unchanged evidence, obtain `STATUS: PASS`, then use the linear sync process and push the selected work.
- REQ-SIMD-015: At every bootstrap phase, actually launch that phase's admitted compiler/interpreter and cached MCP, LSP MCP, SPipe plugin, LLM Caret, and DevHub artifacts. Pair their applicable suites with protocol/capability sanity. Verify authenticated read access through DevHub to GitHub, Jira, and Confluence independently; a configured credential or `auth status` exit zero is insufficient. Retain missing artifact, command, plugin, credential, endpoint, and read-scope rows as non-passing owned blockers with exact resume commands.

## Acceptance criteria

- AC-01: Cross-backend conformance fixtures prove scalar-equivalent results for each implemented ISA and vector-width family.
- AC-02: Forced-backend negative fixtures prove unsupported capabilities cannot execute or silently fall back under strict mode.
- AC-03: Database and HTTP benchmarks identify the selected backend and preserve correctness hashes.
- AC-04: A fresh Stage 4 bootstrap passes the bounded essential-tools smoke and the applicable full compiler/lib checks.
- AC-05: Simple and both MCP servers run from the exact freshly admitted cached native artifacts.
- AC-06: The compiler/interpreter phase matrix includes MCP, LSP MCP, SPipe, DevHub, and Caret checks plus every phase-supported test suite, with no placeholder pass.
- AC-07: Every unavailable target row remains active as blocked/unsupported evidence with prerequisites, exact resume command, artifacts, owner, and reviewer.
- AC-08: Final verification traces every requirement to executable evidence and reports `STATUS: PASS` before push.
- AC-09: The Phase 1, 2, 3, and 4 records each contain actual-launch, plugin, Caret, DevHub, GitHub, Jira, and Confluence rows. Each PASS proves the exact phase artifact ran and returned a validated response; unsupported/unconfigured rows cannot pass through another phase, a fixture, help output, or a static source scan.

REQ-SIMD-015 and AC-09 are the user's explicit 2026-09-08 refinement; Option A and NFR Profile 2 remain selected.
