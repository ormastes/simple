# SimpleOS Libc Shim — Build system
#
# Produces libsimpleos_c.a for linking into freestanding x86_64 binaries.
#
# Usage:
#   make                 # build libsimpleos_c.a
#   make clean           # remove build artifacts

CC      = clang
AR      = ar
CFLAGS  = -target x86_64-unknown-none-elf \
          -ffreestanding -nostdlib -fno-builtin \
          -mno-red-zone -fno-stack-protector -fno-exceptions \
          -fno-unwind-tables -fno-asynchronous-unwind-tables \
          -O2 -Wall -Wextra -Wno-unused-parameter \
          -I include

ASFLAGS = -target x86_64-unknown-none-elf \
          -ffreestanding -nostdlib

C_SRCS  = simpleos_libc.c simpleos_math.c simpleos_math_ext.c simpleos_fs.c \
          simpleos_pthread.c simpleos_alloc.c simpleos_process.c \
          simpleos_string_ext.c simpleos_stdlib_ext.c \
          simpleos_time.c simpleos_printf_float.c simpleos_cxxabi.c \
          simpleos_dlmalloc.c simpleos_signal.c
ASM_SRCS = simpleos_crt0.S simpleos_syscall.S simpleos_setjmp.S

C_OBJS  = $(C_SRCS:.c=.o)
ASM_OBJS = $(ASM_SRCS:.S=.o)
OBJS    = $(C_OBJS) $(ASM_OBJS)

TARGET  = libsimpleos_c.a

.PHONY: all clean

all: $(TARGET)

$(TARGET): $(OBJS)
	$(AR) rcs $@ $^

%.o: %.c simpleos_libc.h
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(CC) $(ASFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(TARGET)
