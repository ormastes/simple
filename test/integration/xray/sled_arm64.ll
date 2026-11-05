; Pure-Simple-style Windows ARM64 entry+exit sled via LLVM IR inline asm.
; Inactive: skip entire 32-byte sled. Active: patch first 4-byte B to NOP.
target triple = "aarch64-pc-windows-msvc"

@simple_sled_map = dso_local constant [2 x ptr] [
    ptr @simple_entry_sled, ptr @simple_exit_sled]
@simple_entry_sled = external global i8
@simple_exit_sled = external global i8

define dso_local i64 @simple_probe(i64 %a, i64 %b) #0 {
entry:
  call void asm sideeffect alignstack
    ".p2align 2\0A.globl simple_entry_sled\0Asimple_entry_sled:\0Ab 1f\0Astp x16, x17, [sp, #-16]!\0Astp x0, x30, [sp, #-16]!\0Amovz w0, #0x1234\0Amovk w0, #0, lsl #16\0Abl simple_trace_entry\0Aldp x0, x30, [sp], #16\0Aldp x16, x17, [sp], #16\0A1:\0A",
    "~{memory}"()
  %result = add i64 %a, %b
  call void asm sideeffect alignstack
    ".p2align 2\0A.globl simple_exit_sled\0Asimple_exit_sled:\0Ab 2f\0Astp x16, x17, [sp, #-16]!\0Astp x0, x30, [sp, #-16]!\0Amovz w0, #0x1234\0Amovk w0, #0, lsl #16\0Abl simple_trace_exit\0Aldp x0, x30, [sp], #16\0Aldp x16, x17, [sp], #16\0A2:\0A",
    "~{memory}"()
  ret i64 %result
}

attributes #0 = { noinline nounwind noredzone }
