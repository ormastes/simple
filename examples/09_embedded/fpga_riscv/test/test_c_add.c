// C test for RV32I GHDL simulation
// Computes factorial(5) = 120, writes to LED register

#define LED_REG (*(volatile unsigned int*)0x80000000)

int factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; i++)
        result *= i;
    return result;
}

void _start() {
    int result = factorial(5);  // 120
    LED_REG = result;
    asm volatile("ecall");  // halt CPU
}
