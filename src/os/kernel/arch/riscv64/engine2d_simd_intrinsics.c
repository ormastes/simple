#include <stdint.h>

/* This owner compiles with the platform's real rv64gc flags. V instructions
 * live in feature-gated inline-assembly regions and execute only when misa.V
 * is present; unsupported guests return zero chunks and fail closed. */
static uint64_t simpleos_riscv_misa(void) {
    uint64_t value;
    __asm__ volatile("csrr %0, misa" : "=r"(value));
    return value;
}
static int simpleos_has_rvv(void) { return (simpleos_riscv_misa() & (1ull << 21)) != 0; }
static uint64_t simpleos_riscv_vlenb(void) {
    uint64_t value;
    __asm__ volatile(".option push\n.option arch,+v\ncsrr %0, vlenb\n.option pop" : "=r"(value));
    return value;
}
static uint64_t simpleos_arch_feature(void) { return simpleos_has_rvv() ? 4u : 0u; }
static uint64_t simpleos_arch_vector_width(void) { return simpleos_has_rvv() ? simpleos_riscv_vlenb() * 8u : 0u; }
static uint64_t simpleos_vector_lanes(void) { return simpleos_has_rvv() ? simpleos_riscv_vlenb() / 4u : 0u; }

static uint64_t simpleos_vector_fill(uint32_t *dst, uint64_t count, uint32_t color) {
    if (!simpleos_has_rvv()) return 0;
    uint64_t lanes = simpleos_vector_lanes(), chunks = 0, i = 0;
    while (i + lanes <= count) {
        __asm__ volatile(
            ".option push\n.option arch,+v\nvsetvli zero, %[vl], e32, m1, ta, ma\nvmv.v.x v0, %[color]\nvse32.v v0, (%[dst])\n.option pop"
            :: [vl] "r"(lanes), [color] "r"(color), [dst] "r"(dst + i) : "memory");
        i += lanes;
        chunks += 1u;
    }
    for (; i < count; i++) dst[i] = color;
    return chunks;
}
static uint64_t simpleos_vector_copy(uint32_t *dst, const uint32_t *src, uint64_t count) {
    if (!simpleos_has_rvv()) return 0;
    uint64_t lanes = simpleos_vector_lanes(), chunks = 0, i = 0;
    while (i + lanes <= count) {
        __asm__ volatile(
            ".option push\n.option arch,+v\nvsetvli zero, %[vl], e32, m1, ta, ma\nvle32.v v0, (%[src])\nvse32.v v0, (%[dst])\n.option pop"
            :: [vl] "r"(lanes), [src] "r"(src + i), [dst] "r"(dst + i) : "memory");
        i += lanes;
        chunks += 1u;
    }
    for (; i < count; i++) dst[i] = src[i];
    return chunks;
}
static uint32_t simpleos_scalar_blend(uint32_t src, uint32_t dst);
static uint64_t simpleos_vector_blend(uint32_t *dst, const uint32_t *src, uint64_t count) {
    if (!simpleos_has_rvv()) return 0;
    uint64_t lanes = simpleos_vector_lanes(), chunks = 0, i = 0;
    while (i + lanes <= count) {
        __asm__ volatile(
            ".option push\n.option arch,+v\n"
            "vsetvli zero, %[vl], e32, m1, ta, ma\n"
            "vle32.v v0, (%[src])\nvle32.v v1, (%[dst])\n"
            "vsrl.vi v2, v0, 24\nvrsub.vx v3, v2, %[full]\n"
            "vsrl.vi v4, v0, 16\nvand.vx v4, v4, %[full]\n"
            "vsrl.vi v5, v1, 16\nvand.vx v5, v5, %[full]\n"
            "vmul.vv v4, v4, v2\nvmacc.vv v4, v5, v3\n"
            "vsrl.vi v5, v4, 8\nvadd.vi v4, v4, 1\nvadd.vv v4, v4, v5\nvsrl.vi v4, v4, 8\nvsll.vi v4, v4, 16\n"
            "vsrl.vi v5, v0, 8\nvand.vx v5, v5, %[full]\n"
            "vsrl.vi v6, v1, 8\nvand.vx v6, v6, %[full]\n"
            "vmul.vv v5, v5, v2\nvmacc.vv v5, v6, v3\n"
            "vsrl.vi v6, v5, 8\nvadd.vi v5, v5, 1\nvadd.vv v5, v5, v6\nvsrl.vi v5, v5, 8\nvsll.vi v5, v5, 8\nvor.vv v4, v4, v5\n"
            "vand.vx v5, v0, %[full]\nvand.vx v6, v1, %[full]\n"
            "vmul.vv v5, v5, v2\nvmacc.vv v5, v6, v3\n"
            "vsrl.vi v6, v5, 8\nvadd.vi v5, v5, 1\nvadd.vv v5, v5, v6\nvsrl.vi v5, v5, 8\nvor.vv v4, v4, v5\n"
            "vor.vx v4, v4, %[alpha]\nvse32.v v4, (%[dst])\n.option pop"
            :: [vl] "r"(lanes), [src] "r"(src + i), [dst] "r"(dst + i),
               [full] "r"(255u), [alpha] "r"(0xff000000u) : "memory");
        i += lanes;
        chunks += 1u;
    }
    for (; i < count; i++) dst[i] = simpleos_scalar_blend(src[i], dst[i]);
    return chunks;
}

#define SIMPLEOS_SIMD_PREFIX rt_simpleos_rvv_engine2d_simd
#include "../../../compositor/engine2d_simd_intrinsic_owner.inc"
