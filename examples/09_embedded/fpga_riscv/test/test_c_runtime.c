// C test for RV32I GHDL simulation - runtime computation
// Uses volatile to prevent constant folding
// Computes sum(1..10) = 55 at runtime

#define LED_REG (*(volatile unsigned int*)0x80000000)
#define SW_REG  (*(volatile unsigned int*)0x80000004)

void _start() __attribute__((section(".text.start")));

void _start() {
    volatile int n = 10;  // prevent constant folding
    int sum = 0;
    for (int i = 1; i <= n; i++)
        sum += i;
    LED_REG = sum;  // 55
    asm volatile("ecall");
}
