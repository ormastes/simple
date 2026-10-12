# HIR diagnostic truncation materializes the whole input

Status: confirmed source mechanism; bounded repair and runtime qualification pending. Bug DB reconciliation pending because no qualified writer is available. Canonical ID: `hir_diagnostic_text_iteration_unbounded_allocation`.

The initial `driver_hir_diagnostic_v1.spl` encoder limits retained output to 4,096 UTF-8 bytes, but iterates `for character in reason` before breaking at that boundary. This does not bound preparatory allocation or processing.

Pure Simple's `src/compiler/50.mir/mir_lowering_stmts.spl` text iteration emits `rt_string_chars` on the entire collection before its counted array loop. The core-C implementation in `src/runtime/runtime_native.c` reserves an array using the original string byte length and creates a string for every codepoint before returning. A long diagnostic therefore causes work and allocations proportional to the entire input despite the output cap. `text_byte_len` itself is constant time and is not the cause.

The locally applied helper identity is `58b8da1dfa926f9e15e37e6c8eb4c379b16731400b016fa5d875053fba16767d`. Its new compiler caller integration is still private and unrun. Existing immutable producer/source capsules are unchanged; this report does not establish that the helper caused any historical crash or measured regression.

Repair must bound the input before character iteration while preserving UTF-8 scalar boundaries. A candidate can inspect at most the output limit plus three lookahead bytes, provided the actual substring implementation performs a bounded copy. Do not use a helper that converts the entire original string to bytes first. Preserve original input byte length, exact retained digest and framing, and the terminal outcome when optional diagnostic publication fails.

Acceptance requires genuine owner execution for ASCII and multibyte boundaries, including a four-byte scalar crossing the cap, and bounded allocation/processing evidence on increasing inputs. Measure time and memory together; a bounded retained record alone does not prove either. The three-cycle diagnostic feature is closed with the repair on HOLD. Native compiler integration and performance publication remain pending.

## Prefix repair boundary

The pure MIR unresolved `substring`/`slice` fallback converts text for `spl_str_slice`. The actual `src/runtime/runtime_legacy_core.c` implementation calls `strlen` on the entire input before copying the requested span. A bounded substring therefore removes full-input character-array allocation but still performs an input-length scan on that path. The existing tagged `rt_slice` implementation is a separate owner surface; interpreter registration and lowering compatibility must be established before substituting it. Do not present the pending prefix memory repair as constant-time processing or a qualified compile-speed improvement.

The final private prefix candidate passed its ASCII boundary case but failed both Unicode boundary cases with a partial UTF-8 `StrBytes` value that could not be iterated. Its terminal receipt is `7c1c4fbe` (prefix), under `build/native_probe/hir-diagnostic-retention-20261012-astra`. The candidate was not applied. Do not weaken the Unicode oracle, integrate the current unbounded helper into compiler callers, or publish a memory/performance improvement. A future repair must validate or trim the bounded prefix to a complete scalar boundary before iteration and establish the actual runtime owner contract.
