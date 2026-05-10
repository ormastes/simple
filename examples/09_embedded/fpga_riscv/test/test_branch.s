# Test branches: if 10 > 5, LED = 42; else LED = 99
# Expected: LED = 42

.section .text
.globl _start
_start:
    li   a0, 10
    li   a1, 5
    blt  a1, a0, greater   # 5 < 10 => branch taken
    li   a2, 99            # should NOT execute
    j    done
greater:
    li   a2, 42            # should execute
done:
    lui  t0, 0x80000
    sw   a2, 0(t0)         # LED = 42
    ecall
