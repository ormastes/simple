#include <stdint.h>

static inline void simpleos_x86_outb(uint16_t port, uint8_t value)
{
    __asm__ volatile("outb %0, %1" : : "a"(value), "Nd"(port) : "memory");
}

void simpleos_x86_interrupt_disable(void)
{
    __asm__ volatile("cli" : : : "memory");
}

void simpleos_x86_interrupt_enable(void)
{
    __asm__ volatile("sti" : : : "memory");
}

void simpleos_x86_halt_until_interrupt(void)
{
    __asm__ volatile("hlt" : : : "memory");
}

void simpleos_x86_pic_mask_all(void)
{
    simpleos_x86_outb(0x21u, 0xFFu);
    simpleos_x86_outb(0xA1u, 0xFFu);
}
