# ──────────────────────────────────────────────────────────────────────
# SimpleOS — L4 Microkernel Reference Implementation
# ref/Makefile — Multi-architecture build system (clang cross-compilation)
#
# Usage:
#   make                   # default: all-x86
#   make all-x86_64
#   make all-arm32
#   make all-aarch64
#   make all-riscv32
#   make all-riscv64
#   make all-arches        # build all 6
#   make clean
# ──────────────────────────────────────────────────────────────────────

# ── Toolchain ─────────────────────────────────────────────────────────
CC       := clang
AS       := clang
LD       := ld.lld
OBJCOPY  := llvm-objcopy
OBJDUMP  := llvm-objdump
SIZE     := llvm-size

# ── Common flags ──────────────────────────────────────────────────────
CFLAGS_COMMON  := -O2 -ffreestanding -nostdlib -nostdinc \
                  -Wall -Wextra -Wno-unused-parameter -Wno-unused-function \
                  -fno-stack-protector -fno-pic -fno-pie \
                  -I. -Icommon
ASFLAGS_COMMON := -ffreestanding -nostdlib -I. -Icommon

# ── Architecture definitions ─────────────────────────────────────────

ARCH_x86_TRIPLE      := --target=i686-unknown-none-elf
ARCH_x86_CFLAGS      := -m32
ARCH_x86_LDFLAGS     := -m elf_i386
ARCH_x86_LINKER      := arch/x86/linker.ld

ARCH_x86_64_TRIPLE   := --target=x86_64-unknown-none-elf
ARCH_x86_64_CFLAGS   := -m64 -mcmodel=kernel -mno-red-zone
ARCH_x86_64_LDFLAGS  := -m elf_x86_64
ARCH_x86_64_LINKER   := arch/x86_64/linker.ld

ARCH_arm32_TRIPLE    := --target=armv7a-none-eabi
ARCH_arm32_CFLAGS    := -marm -mfloat-abi=soft
ARCH_arm32_LDFLAGS   :=
ARCH_arm32_LINKER    := arch/arm32/linker.ld

ARCH_aarch64_TRIPLE  := --target=aarch64-unknown-none-elf
ARCH_aarch64_CFLAGS  :=
ARCH_aarch64_LDFLAGS :=
ARCH_aarch64_LINKER  := arch/aarch64/linker.ld

ARCH_riscv32_TRIPLE  := --target=riscv32-unknown-none-elf
ARCH_riscv32_CFLAGS  := -march=rv32imac -mabi=ilp32 -mcmodel=medany
ARCH_riscv32_LDFLAGS :=
ARCH_riscv32_LINKER  := arch/riscv32/linker.ld

ARCH_riscv64_TRIPLE  := --target=riscv64-unknown-none-elf
ARCH_riscv64_CFLAGS  := -march=rv64imac -mabi=lp64 -mcmodel=medany
ARCH_riscv64_LDFLAGS :=
ARCH_riscv64_LINKER  := arch/riscv64/linker.ld

# ── Source discovery (use shell find since Make wildcard doesn't support **) ──
KERNEL_C_SRCS := $(shell find kernel -name '*.c' 2>/dev/null)
COMMON_C_SRCS := $(shell find common -name '*.c' 2>/dev/null)

# ── Default target ────────────────────────────────────────────────────
.PHONY: all
all: all-x86

# ── Per-architecture build template ──────────────────────────────────
# $(1) = arch name (x86, x86_64, arm32, aarch64, riscv32, riscv64)
define ARCH_template

BUILDDIR_$(1) := build/$(1)

# Architecture-specific sources
ARCH_C_SRCS_$(1)  := $$(shell find arch/$(1) -name '*.c' 2>/dev/null)
ARCH_S_SRCS_$(1)  := $$(shell find arch/$(1) -name '*.S' 2>/dev/null)

# Object files
KERNEL_OBJS_$(1)  := $$(patsubst %.c,$$(BUILDDIR_$(1))/%.o,$$(KERNEL_C_SRCS))
COMMON_OBJS_$(1)  := $$(patsubst %.c,$$(BUILDDIR_$(1))/%.o,$$(COMMON_C_SRCS))
ARCH_C_OBJS_$(1)  := $$(patsubst %.c,$$(BUILDDIR_$(1))/%.o,$$(ARCH_C_SRCS_$(1)))
ARCH_S_OBJS_$(1)  := $$(patsubst %.S,$$(BUILDDIR_$(1))/%.o,$$(ARCH_S_SRCS_$(1)))
ALL_OBJS_$(1)     := $$(KERNEL_OBJS_$(1)) $$(COMMON_OBJS_$(1)) $$(ARCH_C_OBJS_$(1)) $$(ARCH_S_OBJS_$(1))

# Resolved flags
CFLAGS_$(1)  := $$(CFLAGS_COMMON) $$(ARCH_$(1)_TRIPLE) $$(ARCH_$(1)_CFLAGS)
ASFLAGS_$(1) := $$(ASFLAGS_COMMON) $$(ARCH_$(1)_TRIPLE) $$(ARCH_$(1)_CFLAGS)
LDFLAGS_$(1) := -nostdlib $$(ARCH_$(1)_LDFLAGS)

# Kernel ELF output
KERNEL_ELF_$(1) := $$(BUILDDIR_$(1))/kernel.elf

.PHONY: all-$(1) objs-$(1)
all-$(1): $$(KERNEL_ELF_$(1))

# Compile-only target (skip link, useful for syntax checking)
objs-$(1): $$(ALL_OBJS_$(1))
	@echo "[OBJS]  $(1): $$(words $$(ALL_OBJS_$(1))) objects built"

# Link
$$(KERNEL_ELF_$(1)): $$(ALL_OBJS_$(1))
	@mkdir -p $$(dir $$@)
	$$(LD) $$(LDFLAGS_$(1)) -T $$(ARCH_$(1)_LINKER) -o $$@ $$^
	@echo "[LINK]  $$@"
	@$$(SIZE) $$@ 2>/dev/null || size $$@ 2>/dev/null || true

# Compile C → .o
$$(BUILDDIR_$(1))/%.o: %.c
	@mkdir -p $$(dir $$@)
	$$(CC) $$(CFLAGS_$(1)) -c -o $$@ $$<

# Assemble .S → .o
$$(BUILDDIR_$(1))/%.o: %.S
	@mkdir -p $$(dir $$@)
	$$(AS) $$(ASFLAGS_$(1)) -c -o $$@ $$<

endef

# ── Instantiate for every architecture ────────────────────────────────
$(eval $(call ARCH_template,x86))
$(eval $(call ARCH_template,x86_64))
$(eval $(call ARCH_template,arm32))
$(eval $(call ARCH_template,aarch64))
$(eval $(call ARCH_template,riscv32))
$(eval $(call ARCH_template,riscv64))

# ── Convenience: build all architectures ──────────────────────────────
.PHONY: all-arches
all-arches: all-x86 all-x86_64 all-arm32 all-aarch64 all-riscv32 all-riscv64

# ── Clean ─────────────────────────────────────────────────────────────
.PHONY: clean
clean:
	rm -rf build/
	@echo "[CLEAN] build/"
