#ifndef SIMPLE_LLD_SHIM_H
#define SIMPLE_LLD_SHIM_H

#ifdef __cplusplus
extern "C" {
#endif

/* Invoke the in-process LLD ELF driver.
 *
 * argv:         NULL-terminated argv array, first element should be "ld.lld".
 * stderr_buf:   Optional buffer to capture stderr output. May be NULL.
 * stderr_cap:   Capacity of stderr_buf in bytes (ignored if NULL).
 *
 * Returns: 0 on success, nonzero on linker error.
 *
 * Implementation calls lld::elf::link (or lld::lldMain) with exitEarly=false,
 * disableOutput=false.
 */
int simple_lld_elf_link(const char* const* argv,
                        char* stderr_buf,
                        int stderr_cap);

#ifdef __cplusplus
}
#endif

#endif /* SIMPLE_LLD_SHIM_H */
