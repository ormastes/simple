# QEMU debug hexadecimal parser compares text with integer codes

Status: confirmed Phase 1 failure; minimal source repair passed the focused
hexadecimal regression **1/1** in cycle two. Release gates remain unverified.
Owner: `src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl`,
`parse_hex_value_u64`.

## Executed evidence

`test/03_system/hardware/t32_tools/qemu_boot_spec.spl` executed five examples
in the admitted Phase 1 diagnostic producer: four formatters passed and the
real hexadecimal parser failed. Exact error:
`semantic: type mismatch: comparing string with integer`.

Log: `build/phase-one-ui-diagnostic/qemu_boot_spec/cycle-one.log`.
Producer/source manifest: `build/phase-one-ui-diagnostic/hardware-helpers-inputs.json`.
Summary: 5 executed, 4 passed, 1 failed, 274ms. These are producer-bound Phase 1
results; they do not qualify the self-hosted runtime or a release.

The sibling TRACE32 registry/configuration spec passed 4/4 in 244ms; its log
is `build/phase-one-ui-diagnostic/trace32_wrapper_spec/cycle-one.log`. It does
not need repeating for this isolated parser edit.

## Root cause and repair

The parser loops to `clean.len()` (UTF-8 bytes), gets `clean.char_at(i)` (text),
and compares that value with integer ASCII ranges. The comparison fails on
valid hexadecimal input. Merely changing the accessor to `char_code_at` would
still combine codepoint indexing with a byte-count bound.

The repair changes that one accessor to `clean.byte_at(i)`. Both the seed's
`interpreter_method/string.rs` byte accessor and the pure-Simple evaluator's
`compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl`
return a numeric byte, matching the loop and ASCII hexadecimal algorithm.
Two comments document the numeric representation and permissive fallback.

No prefix, accumulation, formatter, GDB stub, transport or runtime code changed.
The existing algorithm initializes each digit to zero: bytes outside 0–9,
a–f and A–F still contribute zero while multiplying the accumulator by 16.
It therefore remains permissive (for example, an invalid ASCII `g` contributes
zero); it does not become a validating parser. There is still no explicit
arithmetic-overflow check. This report documents these limitations without
claiming invalid/non-ASCII/overflow execution coverage.

## Focused verification and remaining gates

The parent ran only the previously failed hexadecimal scenario, extracted from
the canonical source, as cycle two: **1/1 PASS**, 477ms, exit 0. It covers zero,
numeric, alphabetic, uppercase prefix/mixed case, leading zero, and unprefixed
addresses. Evidence:
`build/phase-one-ui-diagnostic/qemu-hex-cycle-two_spec/cycle-two.log` and run
receipts, `build/phase-one-ui-diagnostic/qemu-hex-repair-inputs.json`, and
`build/phase-one-ui-diagnostic/qemu-hex-repair.patch`.

The four passing formatter examples and TRACE32 spec were not rerun. Evidence
is four formatter passes at the baseline snapshot plus one focused parser pass
at the repaired snapshot; this is **not** a complete five-scenario rerun against
one repaired source snapshot. This documentation update performed no execution.

This library change also requires the repository's self-hosted compiler/lib,
MCP and LSP checks, MCP stdio integration, core runtime smoke and MCP native
smoke before release qualification. They remain **UNVERIFIED** because the
available self-hosted artifact lacks the required full CLI/test surfaces;
the Phase 1 seed result is not a substitute for those gates. SPipe docgen also
remains unverified. Native probe, QEMU boot and live GDB behavior are outside
the evidence established by this helper repair.
