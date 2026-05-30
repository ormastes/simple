# Makefile — rv64_fpga_hello bare-metal FPGA hello payload
# Delegates to build.shs for the actual build logic.

.PHONY: all clean flash

all:
	sh build.shs

clean:
	sh build.shs clean

# BLOCKED: flash requires OpenOCD + FPGA probe configuration.
# See doc/03_plan/agent_tasks/riscv64_fpga_simpleos_launch.md for HW setup.
flash:
	@echo "BLOCKED: flash target requires OpenOCD + JTAG probe."
	@echo "  Configure: openocd -f board/ml_carrier_card.cfg"
	@echo "  Then:      load_image rv64_fpga_hello.elf 0x80000000 elf"
	@exit 1
