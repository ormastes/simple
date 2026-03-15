# x86 ISR Entry Stubs
#
# 256 Interrupt Service Routine stubs.
# Each stub pushes its vector number onto the stack and jumps to a
# common handler that saves all registers, calls the Simple-language
# trap_handler(), restores registers, and returns via iret.
#
# Vectors that the CPU pushes an error code for:
#   8 (Double Fault), 10 (Invalid TSS), 11 (Segment Not Present),
#   12 (Stack-Segment Fault), 13 (General Protection), 14 (Page Fault),
#   17 (Alignment Check), 21 (Control Protection),
#   29 (VMM Communication), 30 (Security Exception)
# All other vectors get a dummy error code of 0.

.section .text
.code32

# ---------- Macro: ISR stub WITHOUT error code ----------
.macro ISR_NOERR vector
    .global isr_stub_\vector
    .align 4
    isr_stub_\vector:
        push $0                 # dummy error code
        push $\vector           # vector number
        jmp isr_common
.endm

# ---------- Macro: ISR stub WITH error code (CPU pushes it) ----------
.macro ISR_ERR vector
    .global isr_stub_\vector
    .align 4
    isr_stub_\vector:
        # error code already on stack from CPU
        push $\vector           # vector number
        jmp isr_common
.endm

# ---------- Generate stubs for vectors 0-31 (CPU exceptions) ----------

ISR_NOERR 0    # Division Error
ISR_NOERR 1    # Debug
ISR_NOERR 2    # NMI
ISR_NOERR 3    # Breakpoint
ISR_NOERR 4    # Overflow
ISR_NOERR 5    # Bound Range Exceeded
ISR_NOERR 6    # Invalid Opcode
ISR_NOERR 7    # Device Not Available
ISR_ERR   8    # Double Fault
ISR_NOERR 9    # Coprocessor Segment Overrun
ISR_ERR   10   # Invalid TSS
ISR_ERR   11   # Segment Not Present
ISR_ERR   12   # Stack-Segment Fault
ISR_ERR   13   # General Protection Fault
ISR_ERR   14   # Page Fault
ISR_NOERR 15   # Reserved
ISR_NOERR 16   # x87 Floating-Point Exception
ISR_ERR   17   # Alignment Check
ISR_NOERR 18   # Machine Check
ISR_NOERR 19   # SIMD Floating-Point Exception
ISR_NOERR 20   # Virtualization Exception
ISR_ERR   21   # Control Protection Exception
ISR_NOERR 22   # Reserved
ISR_NOERR 23   # Reserved
ISR_NOERR 24   # Reserved
ISR_NOERR 25   # Reserved
ISR_NOERR 26   # Reserved
ISR_NOERR 27   # Reserved
ISR_NOERR 28   # Hypervisor Injection Exception
ISR_ERR   29   # VMM Communication Exception
ISR_ERR   30   # Security Exception
ISR_NOERR 31   # Reserved

# ---------- Generate stubs for vectors 32-255 (IRQs + software) ----------

# IRQ 0-15  -> vectors 32-47
ISR_NOERR 32
ISR_NOERR 33
ISR_NOERR 34
ISR_NOERR 35
ISR_NOERR 36
ISR_NOERR 37
ISR_NOERR 38
ISR_NOERR 39
ISR_NOERR 40
ISR_NOERR 41
ISR_NOERR 42
ISR_NOERR 43
ISR_NOERR 44
ISR_NOERR 45
ISR_NOERR 46
ISR_NOERR 47

# Vectors 48-127 (unused, but stubs prevent triple-fault)
.irp i, 48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63
    ISR_NOERR \i
.endr
.irp i, 64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79
    ISR_NOERR \i
.endr
.irp i, 80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95
    ISR_NOERR \i
.endr
.irp i, 96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111
    ISR_NOERR \i
.endr
.irp i, 112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127
    ISR_NOERR \i
.endr

# Vector 128 (0x80) = syscall (already generated above in 80-95 range)

# Vectors 129-255
.irp i, 129,130,131,132,133,134,135,136,137,138,139,140,141,142,143
    ISR_NOERR \i
.endr
.irp i, 144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159
    ISR_NOERR \i
.endr
.irp i, 160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175
    ISR_NOERR \i
.endr
.irp i, 176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191
    ISR_NOERR \i
.endr
.irp i, 192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207
    ISR_NOERR \i
.endr
.irp i, 208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223
    ISR_NOERR \i
.endr
.irp i, 224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239
    ISR_NOERR \i
.endr
.irp i, 240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255
    ISR_NOERR \i
.endr

# ---------- Common ISR handler ----------

.global isr_common
.align 16
isr_common:
    # Save all general-purpose registers
    pusha

    # Save data segment
    mov %ds, %ax
    push %eax

    # Load kernel data segment
    mov $0x10, %ax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %fs
    mov %ax, %gs

    # Push pointer to the trap frame (stack pointer) as argument
    push %esp

    # Call the Simple-language trap handler
    .extern trap_handler
    call trap_handler

    # Clean up the argument
    add $4, %esp

    # Restore data segment
    pop %eax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %fs
    mov %ax, %gs

    # Restore general-purpose registers
    popa

    # Remove vector number and error code from stack
    add $8, %esp

    # Return from interrupt
    iret

# ---------- ISR stub address table ----------
# This table is read by idt.spl to populate the IDT.

.section .rodata
.global isr_stub_table
.align 4
isr_stub_table:
    .long isr_stub_0,   isr_stub_1,   isr_stub_2,   isr_stub_3
    .long isr_stub_4,   isr_stub_5,   isr_stub_6,   isr_stub_7
    .long isr_stub_8,   isr_stub_9,   isr_stub_10,  isr_stub_11
    .long isr_stub_12,  isr_stub_13,  isr_stub_14,  isr_stub_15
    .long isr_stub_16,  isr_stub_17,  isr_stub_18,  isr_stub_19
    .long isr_stub_20,  isr_stub_21,  isr_stub_22,  isr_stub_23
    .long isr_stub_24,  isr_stub_25,  isr_stub_26,  isr_stub_27
    .long isr_stub_28,  isr_stub_29,  isr_stub_30,  isr_stub_31
    .long isr_stub_32,  isr_stub_33,  isr_stub_34,  isr_stub_35
    .long isr_stub_36,  isr_stub_37,  isr_stub_38,  isr_stub_39
    .long isr_stub_40,  isr_stub_41,  isr_stub_42,  isr_stub_43
    .long isr_stub_44,  isr_stub_45,  isr_stub_46,  isr_stub_47
    .long isr_stub_48,  isr_stub_49,  isr_stub_50,  isr_stub_51
    .long isr_stub_52,  isr_stub_53,  isr_stub_54,  isr_stub_55
    .long isr_stub_56,  isr_stub_57,  isr_stub_58,  isr_stub_59
    .long isr_stub_60,  isr_stub_61,  isr_stub_62,  isr_stub_63
    .long isr_stub_64,  isr_stub_65,  isr_stub_66,  isr_stub_67
    .long isr_stub_68,  isr_stub_69,  isr_stub_70,  isr_stub_71
    .long isr_stub_72,  isr_stub_73,  isr_stub_74,  isr_stub_75
    .long isr_stub_76,  isr_stub_77,  isr_stub_78,  isr_stub_79
    .long isr_stub_80,  isr_stub_81,  isr_stub_82,  isr_stub_83
    .long isr_stub_84,  isr_stub_85,  isr_stub_86,  isr_stub_87
    .long isr_stub_88,  isr_stub_89,  isr_stub_90,  isr_stub_91
    .long isr_stub_92,  isr_stub_93,  isr_stub_94,  isr_stub_95
    .long isr_stub_96,  isr_stub_97,  isr_stub_98,  isr_stub_99
    .long isr_stub_100, isr_stub_101, isr_stub_102, isr_stub_103
    .long isr_stub_104, isr_stub_105, isr_stub_106, isr_stub_107
    .long isr_stub_108, isr_stub_109, isr_stub_110, isr_stub_111
    .long isr_stub_112, isr_stub_113, isr_stub_114, isr_stub_115
    .long isr_stub_116, isr_stub_117, isr_stub_118, isr_stub_119
    .long isr_stub_120, isr_stub_121, isr_stub_122, isr_stub_123
    .long isr_stub_124, isr_stub_125, isr_stub_126, isr_stub_127
    .long isr_stub_128, isr_stub_129, isr_stub_130, isr_stub_131
    .long isr_stub_132, isr_stub_133, isr_stub_134, isr_stub_135
    .long isr_stub_136, isr_stub_137, isr_stub_138, isr_stub_139
    .long isr_stub_140, isr_stub_141, isr_stub_142, isr_stub_143
    .long isr_stub_144, isr_stub_145, isr_stub_146, isr_stub_147
    .long isr_stub_148, isr_stub_149, isr_stub_150, isr_stub_151
    .long isr_stub_152, isr_stub_153, isr_stub_154, isr_stub_155
    .long isr_stub_156, isr_stub_157, isr_stub_158, isr_stub_159
    .long isr_stub_160, isr_stub_161, isr_stub_162, isr_stub_163
    .long isr_stub_164, isr_stub_165, isr_stub_166, isr_stub_167
    .long isr_stub_168, isr_stub_169, isr_stub_170, isr_stub_171
    .long isr_stub_172, isr_stub_173, isr_stub_174, isr_stub_175
    .long isr_stub_176, isr_stub_177, isr_stub_178, isr_stub_179
    .long isr_stub_180, isr_stub_181, isr_stub_182, isr_stub_183
    .long isr_stub_184, isr_stub_185, isr_stub_186, isr_stub_187
    .long isr_stub_188, isr_stub_189, isr_stub_190, isr_stub_191
    .long isr_stub_192, isr_stub_193, isr_stub_194, isr_stub_195
    .long isr_stub_196, isr_stub_197, isr_stub_198, isr_stub_199
    .long isr_stub_200, isr_stub_201, isr_stub_202, isr_stub_203
    .long isr_stub_204, isr_stub_205, isr_stub_206, isr_stub_207
    .long isr_stub_208, isr_stub_209, isr_stub_210, isr_stub_211
    .long isr_stub_212, isr_stub_213, isr_stub_214, isr_stub_215
    .long isr_stub_216, isr_stub_217, isr_stub_218, isr_stub_219
    .long isr_stub_220, isr_stub_221, isr_stub_222, isr_stub_223
    .long isr_stub_224, isr_stub_225, isr_stub_226, isr_stub_227
    .long isr_stub_228, isr_stub_229, isr_stub_230, isr_stub_231
    .long isr_stub_232, isr_stub_233, isr_stub_234, isr_stub_235
    .long isr_stub_236, isr_stub_237, isr_stub_238, isr_stub_239
    .long isr_stub_240, isr_stub_241, isr_stub_242, isr_stub_243
    .long isr_stub_244, isr_stub_245, isr_stub_246, isr_stub_247
    .long isr_stub_248, isr_stub_249, isr_stub_250, isr_stub_251
    .long isr_stub_252, isr_stub_253, isr_stub_254, isr_stub_255
