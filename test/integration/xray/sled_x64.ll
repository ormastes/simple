; Windows x64 XRay-like sled that does not clobber R10 or any other GPR.
; 13-byte slot: JMP+11 (disabled) / 2-byte NOP (enabled), CALL, JMP+4, ID.
; The trampoline obtains ID from the 4 bytes at return_address+2.
target triple = "x86_64-pc-windows-msvc"

@simple_sled_map = dso_local constant [2 x ptr] [
    ptr @simple_entry_sled, ptr @simple_exit_sled]
@simple_entry_sled = external global i8
@simple_exit_sled = external global i8

define dso_local i64 @simple_probe(i64 %a, i64 %b) #0 {
entry:
  call void asm sideeffect alignstack
    ".p2align 1\0A.globl simple_entry_sled\0Asimple_entry_sled:\0A.byte 0xEB,0x0B\0Acall simple_trace_entry\0A.byte 0xEB,0x04\0A.long 0x1234\0A",
    "~{memory}"()
  %result = add i64 %a, %b
  call void asm sideeffect alignstack
    ".p2align 1\0A.globl simple_exit_sled\0Asimple_exit_sled:\0A.byte 0xEB,0x0B\0Acall simple_trace_exit\0A.byte 0xEB,0x04\0A.long 0x1234\0A",
    "~{memory}"()
  ret i64 %result
}

attributes #0 = { noinline nounwind noredzone }
