# OS Drivers Layer Base

`src/os/drivers/**` is MDSOC-only. Do not introduce ECS or MDSOC+ business-world
state. Keep hardware lifecycle, DMA, IRQ, MMIO, and device ownership explicit.
