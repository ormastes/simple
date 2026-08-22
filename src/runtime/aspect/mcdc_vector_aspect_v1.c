/*
 * MC/DC dynamic aspect-pack payload, ABI v1.
 *
 * This translation unit is intentionally outside the default runtime bundle.
 * The aspect-pack artifact producer compiles it as PIC, converts the object to
 * the inner SMF payload, then wraps that payload in SMFAPK.  Consequently a
 * static-off or unselected dynamic build neither links nor maps these bytes.
 */
#include <stdint.h>

extern int32_t rt_mcdc_record_compiled_vector_v1(uint64_t decision_id,
                                                 uint32_t condition_count,
                                                 uint64_t source_digest,
                                                 uint64_t evaluated_mask,
                                                 uint64_t true_mask,
                                                 uint8_t outcome);

#if defined(_WIN32)
#define MCDC_ASPECT_EXPORT __declspec(dllexport)
#else
#define MCDC_ASPECT_EXPORT __attribute__((visibility("default")))
#endif

MCDC_ASPECT_EXPORT const uint8_t
rt_mcdc_aspect_vector_v1__abi_u64_u32_u64_u64_u64_u8_i32_v1 = 1u;

MCDC_ASPECT_EXPORT int32_t
rt_mcdc_aspect_vector_v1(uint64_t decision_id,
                         uint32_t condition_count,
                         uint64_t source_digest,
                         uint64_t evaluated_mask,
                         uint64_t true_mask,
                         uint8_t outcome) {
    return rt_mcdc_record_compiled_vector_v1(decision_id, condition_count,
                                              source_digest, evaluated_mask,
                                              true_mask, outcome);
}
