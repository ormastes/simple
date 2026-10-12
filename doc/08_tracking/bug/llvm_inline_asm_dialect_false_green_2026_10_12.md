# LLVM inline assembly dialect false success

Bug ID: `llvm_inline_asm_dialect_false_green_2026_10_12`. Status: verified source workaround; permanent compiler repair and authoritative bug DB reconciliation pending.

The private Phase1 producer `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1` with matching LLVM 23.1.1 reports errors for bare Intel port instructions, returns successful native-build status, and publishes objects without those instructions. A minimal probe emitted `xor eax,eax; ret` instead of the requested port operations. Process exit and object existence cannot prove correct code generation.

The affected owner is `src/lib/nogc_async_mut_noalloc/baremetal/x86/io.spl`, original SHA256 `164deacd7e8ac5da5c097d11e64d985ec09b205c8c28a4112399380562b27008`. Six tagged calls temporarily surround the unchanged Intel instructions with `.intel_syntax noprefix` and `.att_syntax prefix`. Registers, inputs, outputs, volatile markers and `io_wait` remain unchanged. The restoration directive prevents the assembly mode from leaking into following instructions.

Actual source-owner object checks verify `EE`, `EC`, `66 EF`, `66 ED`, `EF`, `ED` and the `io_wait` operation. No privileged instruction was executed. Original source is retained as RED; explicit Intel directives and valid AT&T controls retain the expected bytes. Native compile and disassembly completed with closed Jobs and unchanged inputs.

Evidence: `build/native_probe/inline-asm-dialect-probe-20261012-astra/`; minimal result SHA256 `97812edafe2e5a422c1d05c8da27a6a5c55e63540345bac6a706571cf2e24de5`; source-owner result SHA256 `4e2f1730cb4a862034d271cb330161bf978b2a2e62fb814b7931cff73ac1b1fa`. LF patch SHA256 `8c9d0fe6125447df487bcc269d4531bc6e585195fb8ecbfef01b0e85b3ab08b0`; LF candidate SHA256 `78c63ccc5ea4238cabab0cd12a2301e33c0b5d9a64579ffa619df763547beabd`. Its only difference from the tested CRLF candidate is line endings.

Recovery reference: `b8b0962d41b54d951cf625b0dc64a6c05fdc22c6`, original owner in the same source path. Actual workaround commit: pending local commit; append its hash after committing. Remote landing remains subject to the user's Phase3 condition.

Permanent repair must propagate assembly dialect correctly and fail object publication/cache admission when LLVM reports assembly errors. Prevention cases must include invalid assembly returning nonzero without a usable artifact, valid AT&T, explicit Intel syntax, each operand width, and adjacent assembly after dialect restoration. Check both Rust seed and pure-Simple emission: the reviewed pure-Simple emitter already transports explicit `intel_syntax`; it must not be changed merely because the seed fails.

Remove only the tagged workaround after applying the permanent repair and verifying the original instruction-byte reproducer. Fetching a repair alone is insufficient. These checks do not qualify privileged hardware execution, universal memory/performance behavior, test products, or full Phase3.
