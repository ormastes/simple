#ifndef SIMPLEOS_X86_64_NONCE_SLOT_CONTRACT_H
#define SIMPLEOS_X86_64_NONCE_SLOT_CONTRACT_H

#include <stddef.h>
#include <stdint.h>

static size_t x86_64_nonce_slot_line_length(const uint8_t *slot, size_t slot_len)
{
    static const char prefix[] = "SIMPLEOS_QEMU_NONCE=";
    if (!slot || slot_len <= sizeof(prefix) || slot_len > 118U) return 0;
    for (size_t i = 0; i + 1U < sizeof(prefix); i++)
        if (slot[i] != (uint8_t)prefix[i]) return 0;
    size_t i = sizeof(prefix) - 1U;
    size_t nonce_begin = i;
    while (i < slot_len && slot[i] != '\n') {
        uint8_t c = slot[i];
        if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
              (c >= '0' && c <= '9') || c == '.' || c == '_' ||
              c == ':' || c == '-')) return 0;
        i++;
    }
    if (i == nonce_begin || i >= slot_len || slot[i] != '\n') return 0;
    size_t line_len = i + 1U;
    for (i = line_len; i < slot_len; i++) if (slot[i] != 0U) return 0;
    return line_len;
}

#endif
