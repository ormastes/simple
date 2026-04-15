// C test for RV32I GHDL simulation (no multiply - pure RV32I)
// Computes sum(1..10) = 55, writes to LED register

#define LED_REG (*(volatile unsigned int*)0x80000000)

void _start() __attribute__((section(".text.start")));

void _start() {
    int sum = 0;
    for (int i = 1; i <= 10; i++)
        sum += i;
    LED_REG = sum;  // 55
    asm volatile("ecall");
}
