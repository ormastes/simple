/* Compile-time guard for the unchanged public C NFC ABI and scalar policy ABI. */
#include <stddef.h>

#include "cosmos_nfc_policy.h"
#include "cosmos_nfc_regs.h"

_Static_assert(sizeof(struct cosmos_nfc_io) == 32U,
               "cosmos_nfc_io ABI changed");
_Static_assert(offsetof(struct cosmos_nfc_io, status_report_address) == 28U,
               "cosmos_nfc_io field order changed");
_Static_assert(sizeof(struct cosmos_nfc_ecc) == 20U,
               "cosmos_nfc_ecc ABI changed");
_Static_assert(offsetof(struct cosmos_nfc_ecc, needs_refresh) == 16U,
               "cosmos_nfc_ecc field order changed");

int (*cosmos_nfc_abi_read_page)(const struct cosmos_nfc_io *,
                                struct cosmos_nfc_ecc *) =
    cosmos_nfc_read_page;
int (*cosmos_nfc_abi_read_page_raw)(const struct cosmos_nfc_io *) =
    cosmos_nfc_read_page_raw;
int (*cosmos_nfc_abi_program_page)(const struct cosmos_nfc_io *) =
    cosmos_nfc_program_page;
int (*cosmos_nfc_abi_erase_block)(unsigned int, unsigned int,
                                  unsigned int, unsigned int) =
    cosmos_nfc_erase_block;
int (*cosmos_nfc_abi_status)(unsigned int, unsigned int, unsigned int,
                             unsigned int *) = cosmos_nfc_status;
int (*cosmos_nfc_abi_decode_ecc)(const volatile unsigned int *,
                                 struct cosmos_nfc_ecc *) =
    cosmos_nfc_decode_ecc;
int (*cosmos_nfc_abi_init)(void) = cosmos_nfc_init;
int (*cosmos_nfc_abi_selftest)(void) = cosmos_nfc_selftest;

int main(void) {
    return cosmos_nfc_abi_read_page == 0 ||
        cosmos_nfc_abi_read_page_raw == 0 ||
        cosmos_nfc_abi_program_page == 0 ||
        cosmos_nfc_abi_erase_block == 0 || cosmos_nfc_abi_status == 0 ||
        cosmos_nfc_abi_decode_ecc == 0 || cosmos_nfc_abi_init == 0 ||
        cosmos_nfc_abi_selftest == 0;
}
