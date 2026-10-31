# Native Result text payload loses its MIR text representation

Status: resolved 2026-10-31 (see below). Focused native regression PASS with rebuilt producer; private-daemon
acceptance and broader compiler checks remain separate pending gates.

Producer SHA-256: `c978ab12656b7bf67d4bf9b6cc6450d08181c9140b19266863e93b3eba57e5f4`.
Runner SHA-256: `e9b8cf88c24d1f694dd4ad2d6e8b4b2fbe042b4dd60147fdc2d194e943acc8f8`.

The plain private-daemon calibration failed before launching a child. The real
secure temporary directory existed, but `secure_temp_dir(parent, prefix)?` was
concatenated as the decimal value `1819984454161`, so creation of `owner.token`
failed. The API correctly returns `Result<text, text>`.

LLDB disassembly of the actual runner shows `rt_enum_payload` at
`private_session_start_v1 +2090`, then `rt_raw_i64_to_string` at `+2125` on that
same result before string concatenation. Evidence is retained in
`D:/dev/simple-runner-next-evidence-20261030/owned46-private-session-disassembly.log`;
the failed run is `accept-plain-green-1793341429788333600` in the same directory.

`lower_try_expr` routes Result success payloads through
`decode_declared_enum_payload_slot`. Its scalar decoder preserved the i64 carrier
for text and only remembered the HIR type. The MIR concatenation path therefore
treated the carrier as an integer. Both static and recovered Result return types
use this decoder.

The repair restores text through `option_text_value` with `bootstrap_text_type`,
matching existing Result `.unwrap()` and Optional `?` handling. The runtime
`rt_interp_cstr` resolves a registered string handle to its data pointer and
preserves raw C string pointers. This restores the native ABI and MIR type;
it does not change the temporary-directory API or suppress errors.

Regression: `test/fixtures/compiler/native_result_try_text_payload.spl` checks
text equality, length, marker concatenation, and unchanged Err propagation.
The rebuilt producer compiled and executed this regression successfully. The
real private-daemon calibration still requires a newly compiled runner.

## Native regression evidence

Producer SHA-256:
`5dd85ea67087e063ae3a68ad0b282c82443e2ade6a178e0f10187fa93028260c`.
The immutable generation-2 source manifest contains 69 paths and has SHA-256
`06a77bfaa0be283ed1ca4a21686697444da3f39a14491f3e0117cdab6cc52beb`.
It includes the original source repair commit
`515b82418683ebc6f5d1fb7efe34964380e88202`, independently reviewed with no blockers.

Receipts reside in
`D:/dev/simple-runner-generation2-evidence-20261030/regression-result-text-01`:
`compiler.sha256`, `identity.env`, `build-status.env`, `run-status.env`,
`build-tree.env`, `run-tree.env`, and `run.stdout`.
Build and execution both exited 0; stdout is exactly `result-try-text: PASS`.
Build peak RSS was 2671356 KiB, peak job commit 2741580 KiB; run peak RSS was
2564 KiB. Both process-tree receipts report quiescence.

This validates heap-built and literal text extraction, equality, length,
concatenation, and Err propagation in the fixture. Shared nested and multi-slot
enum callers were source-reviewed, not independently exercised here. These
receipts do not establish private-daemon startup or broad compiler acceptance.


## Resolved 2026-10-31

Root cause: `lower_try_expr`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, Result
branch) read the Ok payload with `rt_enum_payload` as a raw `i64` and never
restored the declared `ok_type`, so text methods (`trim`, `index_of`) were
unresolved and concatenation stringified the handle.

Fix (already on release/1.0.0 before this resolution; no new compiler change):
`265252279c9` routes the static Result payload through
`decode_declared_enum_payload_slot`; its `Str` arm
(`src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`) restores
text via `option_text_value` (`rt_interp_cstr`) with `bootstrap_text_type`.
`3aa79ca1610` applies the same decoder when the static base type is unknown but
the lowered call remembered its declared Result return. Type aliases need no
MIR handling: HIR expands `type R = Result<text, E>` to the underlying shape
(`src/compiler/20.hir/hir_lowering/type_aliases.spl`).

Test: `test/01_unit/compiler/mir/result_try_text_payload_spec.spl` lowers a
direct and an aliased `Result<text, text>` callee through HIR/MIR and asserts
zero MIR errors, one `rt_string_trim` dispatch, no `rt_raw_i64_to_string`, and
that every `rt_enum_payload` word feeds `rt_interp_cstr`; it also executes the
same shapes in the interpreter (text equality, length, Err propagation). It is
red with the decoder `Str` arm disabled and green with it.

Workarounds removed: the tagged `val ...: text = ...?` annotations in
`src/app/bug/workaround_store.spl` (`load_workarounds_at`,
`workaround_bug_snapshot`, `workaround_refresh_locked`).

Not verified here: native execution of the fixture or of `workaround_store`
with a freshly built stage2 producer (only the Rust seed was available; its
JIT falls back to the interpreter). The 2026-10-30 native receipts above remain
the native evidence.
