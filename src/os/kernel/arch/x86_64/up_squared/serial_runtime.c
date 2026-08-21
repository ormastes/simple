/* UP Squared first-light serial input provider.
 *
 * Output remains owned by the shared freestanding runtime. This board-owned
 * adapter supplies the missing input ABI over the explicitly initialized legacy
 * COM1 candidate. Live CN16 evidence decides whether a later provider must use
 * Apollo Lake LPSS PCI discovery instead.
 */
#include <stdint.h>
#include <stddef.h>

extern uint8_t rt_port_inb(uint16_t port);
extern void rt_port_outb(uint16_t port, uint8_t value);
extern int64_t rt_string_new(int64_t bytes, int64_t length);
extern int64_t rt_string_new_literal(const uint8_t *bytes, uint64_t length);

#define UP2_COM1_BASE 0x3f8u

static uint8_t up2_serial_getchar(void) {
    while ((rt_port_inb((uint16_t)(UP2_COM1_BASE + 5u)) & 0x01u) == 0u) { }
    return rt_port_inb((uint16_t)UP2_COM1_BASE);
}

static void up2_serial_putchar(uint8_t byte) {
    while ((rt_port_inb((uint16_t)(UP2_COM1_BASE + 5u)) & 0x20u) == 0u) { }
    rt_port_outb((uint16_t)UP2_COM1_BASE, byte);
}

long write(int descriptor, const void *buffer, size_t count) {
    if ((descriptor != 1 && descriptor != 2) || buffer == (const void *)0) {
        return -1;
    }
    const uint8_t *bytes = (const uint8_t *)buffer;
    for (size_t index = 0u; index < count; ++index) {
        up2_serial_putchar(bytes[index]);
    }
    return (long)count;
}

int64_t rt_string_new_literal(const uint8_t *bytes, uint64_t length) {
    return rt_string_new((int64_t)(uintptr_t)bytes, (int64_t)length);
}

void serial_println(int64_t value) {
    uintptr_t tagged = (uintptr_t)value;
    if ((tagged & 7u) == 1u) {
        const uint8_t *object = (const uint8_t *)(tagged & ~(uintptr_t)7u);
        uint64_t length = *(const uint64_t *)(object + 8u);
        const uint8_t *bytes = object + 16u;
        for (uint64_t index = 0u; index < length; ++index) {
            up2_serial_putchar(bytes[index]);
        }
    }
    up2_serial_putchar('\r');
    up2_serial_putchar('\n');
}

int64_t rt_serial_readline(void) {
    char line[256];
    uint32_t length = 0;
    while (length < sizeof(line) - 1u) {
        uint8_t byte = up2_serial_getchar();
        if (byte == '\r' || byte == '\n') {
            up2_serial_putchar('\r');
            up2_serial_putchar('\n');
            break;
        }
        if (byte == 0x7fu || byte == '\b') {
            if (length > 0u) {
                length--;
                up2_serial_putchar('\b');
                up2_serial_putchar(' ');
                up2_serial_putchar('\b');
            }
        } else if (byte >= 0x20u) {
            line[length++] = (char)byte;
            up2_serial_putchar(byte);
        }
    }
    line[length] = '\0';
    return rt_string_new_literal((const uint8_t *)line, (uint64_t)length);
}
