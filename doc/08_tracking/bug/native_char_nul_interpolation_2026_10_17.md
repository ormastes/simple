# Native character interpolation loses NUL length through raw C-string concat

Date:2026-10-17
Bug:BUG-NATIVE-CHAR-NUL-INTERPOLATION-20261017
Database registration:pending; no admitted database tool available.
Status:OPEN, actual native failure. NativeChar feature exhausted FINAL cycle3/3; no fourth build/run authorized.
Tested source:699c44fd5a099c9b956dd9142b65da3d102069ba; exact0CD6 producer and own D9 runtime/header proof.

## Actual failure, not a weakened control

The strict candidate FC09D528CA0B2FC4C058E5EA00EEB4E846F46BBF3D93AC993DA99BB6A2B9ED40 linked successfully without FORCE/IGNORE and executed FIRST AND ONLY once. Exit1, stdout49bytes exactly `FAIL unicode-scalar-char: rendered byte length 0` plus newline, stderr0,0.025225seconds, no timeout, identical pre/post executable hash. Actual exclusive ledger, raw outputs and receipt remain under external unicode-scalar-native-char-cycle3/strict-link. The printed0 identifies the input codepoint, not a measured output length. The control observed a length mismatch; zero rendered length is derived below from the actual linked strlen call path.

Sequential ASCII65, BMP233 and supplementary-plane128512 controls completed their native scalar cast-back, actual canonical HirExprKind.CharLit payload match/cast-back and full UTF8 bytes/text checks before reaching codepoint0. NUL scalar and real enum payload cast-backs both passed0; its rendered byte length failed. U+0003 and every later escape, scalar-boundary and invalid-input control were NOT REACHED. No whole Unicode primitive qualification, guard acceptance or generated-codec consumer PASS is claimed.

## Retained code proves the length-losing boundary

Actual fixture COFF unicode_scalar_char_case_v1 loads the real Char i32 scalar at0x269, calls rt_char_from_code at relocation0x26f, converts its managed result through rt_interp_cstr at0x277 and concatenates with rt_strcat at0x282 and0x2a6. The later rendered-byte projection calls rt_string_bytes at0x2d3.

The actual strict map assigns rt_char_from_code, rt_interp_cstr and rt_strcat to runtime_native.obj, and spl_str_concat to runtime_legacy_core.obj. This owner matters: the unused same-name runtime.c definition is not substituted as proof of the linked implementation.

Frozen runtime_native.c:4790 validates the scalar and emits a managed UTF8 string; cp0 writes byte0 with length1. Its rt_interp_cstr at3617 returns only data, dropping that managed length. rt_strcat at7660 delegates to spl_str_concat. The actually linked runtime_legacy_core.c:256-265 measures both inputs with strlen, so a leading NUL becomes length0. This establishes a concrete raw C-string interpolation boundary consistent with the observed failure, rather than evidence that numeric-to-char or enum construction failed.

External nul-render-coff-excerpt.txt and nul-render-owner-proof.json preserve actual instruction offsets, map rows, source head and candidate hash. Full disassembly/object/capsule/runtime/header manifests and every previous attempt remain intact. No binary patch, debugger run or extra execution was used.

## Required faithful repair and acceptance

Fix the compiler-owned interpolation composition boundary so managed text lengths survive scalar rendering and concatenation. Existing rt_strcat_tagged has length-aware managed handling, but merely calling it after rt_interp_cstr would already have lost length. Do not globally change raw rt_strcat ABI: other consumers expect raw pointers. Correct typed call signatures, managed ownership and other interpolation fragments need review before changing this path. This report implements no runtime/compiler repair.

A future admitted repair must retain the exact NUL and U+0003 scalar/payload/byte controls, embedded and leading NUL in surrounding text, ASCII/BMP/nonBMP/escapes, complete scalar extrema and invalid guard denials. No control may be dropped, split into a falsely green scope or relabeled to evade the exhausted budget. Proper generated char-codec fix must still preserve version-specific nil-wire policy and strict Char admission, followed by genuine reader consumer qualification.

No source/helper/fixture/runtime change accompanies this report. Native work STOPPED after3/3. Further work requires an explicitly scoped new authorization and honest existing failure accounting; no automatic fourth attempt.