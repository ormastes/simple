/* Compile beside runtime_native.c with SIMPLE_CORE_C_STANDALONE=0 and =1.
 * Inspect both objects: the C registry owns _c in both modes; only standalone
 * Core-C owns the public name. This consumer also checks the header ABI. */
#include "../runtime.h"

typedef int8_t (*heap_registry_probe_v1)(int64_t);

int8_t rt_heap_ref_registered_provider_header_check(int64_t value) {
#if defined(SIMPLE_CORE_C_STANDALONE) && SIMPLE_CORE_C_STANDALONE
    heap_registry_probe_v1 probe = rt_heap_ref_registered;
#else
    heap_registry_probe_v1 probe = rt_heap_ref_registered_c;
#endif
    return probe(value);
}
