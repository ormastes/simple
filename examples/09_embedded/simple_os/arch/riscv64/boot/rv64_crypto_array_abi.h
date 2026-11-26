#ifndef RV64_CRYPTO_ARRAY_ABI_H
#define RV64_CRYPTO_ARRAY_ABI_H

/* Runtime array ABI bridge for freestanding RV64 & shared x86_64 crypto helpers.
 *
 * Host/baremetal Simple stubs (riscv64/boot/baremetal_stubs.c, baremetal_runtime_core.inc.c,
 * runtime_native.c) expect RAW unshifted lengths and indices in rt_byte_array_new_len(len)
 * and rt_array_get(arr, idx) because compiled Simple loops pass raw counters directly.
 * Conversely, kernel/freestanding_runtime.c decodes rt_index_arg(v) ((v & 7) == 0 ? v >> 3 : v)
 * and x86_64/boot/tls13_aes256_gcm_helper.c's x86_aes_helper_* macros strictly shift >> 3.
 *
 * Probe once at runtime (BSS 0=unprobed, 1=tagged rt_int, 2=raw) by allocating length
 * rt_int(2) (= 16): tagged runtimes return rt_array_len == 2, raw runtimes return 16.
 */
static int g_rv64_crypto_idx_mode = 0;

static spl_i64 rt_int(spl_i64 value) {
    return value << 3;
}

static spl_i64 rt_index_arg(spl_i64 value) {
    return value >> 3;
}

static int rt_crypto_uses_tagged_index(void) {
    if (g_rv64_crypto_idx_mode == 0) {
        spl_i64 probe = rt_byte_array_new_len(rt_int(2));
        spl_i64 probe_len = rt_array_len(probe);
        if (probe_len == 2) {
            g_rv64_crypto_idx_mode = 1;
        } else if (probe_len == 16) {
            g_rv64_crypto_idx_mode = 2;
        } else {
            return 1;
        }
    }
    return g_rv64_crypto_idx_mode == 1;
}

static spl_i64 rt_crypto_encode_len_or_idx(spl_i64 raw) {
    return rt_crypto_uses_tagged_index() ? rt_int(raw) : raw;
}

static spl_i64 rt_crypto_byte_array_new_len(spl_i64 raw_len) {
    return rt_byte_array_new_len(rt_crypto_encode_len_or_idx(raw_len));
}

static spl_i64 rt_crypto_array_get(spl_i64 arr, spl_i64 raw_idx) {
    return rt_array_get(arr, rt_crypto_encode_len_or_idx(raw_idx));
}

static spl_i64 rt_empty_bytes(void) {
    return rt_byte_array_new_len(0);
}

#endif
