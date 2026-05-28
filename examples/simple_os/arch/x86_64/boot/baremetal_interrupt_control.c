typedef unsigned char u8;
typedef unsigned short u16;

static inline void outb(u16 port, u8 value)
{
    __asm__ volatile("outb %0, %1" : : "a"(value), "Nd"(port) : "memory");
}

#define X86_INSN_FN(name, insn) void name(void) { __asm__ volatile(insn : : : "memory"); }
X86_INSN_FN(simpleos_x86_interrupt_disable, "cli")
X86_INSN_FN(simpleos_x86_interrupt_enable, "sti")
X86_INSN_FN(simpleos_x86_halt_until_interrupt, "hlt")

void simpleos_x86_pic_mask_all(void)
{
    outb(0x21u, 0xFFu);
    outb(0xA1u, 0xFFu);
}
