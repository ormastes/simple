/* SOSIX-owned Darwin Seatbelt activation leaf (design
 * doc/05_design/simple_container_macos_seatbelt.md §9.1, §15.2). The ONLY
 * native work is the deprecated libSystem pair
 *     sandbox_init(profile, 0, &error)  +  sandbox_free_error(error)
 * applied to the CALLING process. Profile compilation, admission, error
 * sanitization and the non-Darwin refusal are Simple
 * (std.nogc_async_mut.sosix.darwin_sandbox_v1); this leaf never decides policy.
 *
 * Deliberately not an rt_* runtime primitive: it has no portable meaning, no
 * Rust-lane twin is possible, and only the SOSIX Darwin owner may call it.
 *
 * Receipt [i64], preallocated BEFORE sandbox_init so a successful activation
 * can never be hidden by a later allocation failure:
 *   [0] status: 0 applied, -1 invalid profile, -3 sandbox_init refused,
 *               -4 unsupported host, -6 profile copy allocation failed
 *   [1] error byte count (0..SOSIX_DARWIN_SANDBOX_ERROR_MAX_V1)
 *   [2..] raw platform error bytes, truncated; Simple sanitizes them.
 * NULL only when the receipt itself cannot be allocated; sandbox_init has then
 * NOT run. A refusal is never converted into an unrestricted success. */
#ifndef RUNTIME_SOSIX_DARWIN_SANDBOX_V1_H
#define RUNTIME_SOSIX_DARWIN_SANDBOX_V1_H
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#if defined(__APPLE__)
#include <sandbox.h>
#endif

#define SOSIX_DARWIN_SANDBOX_PROFILE_MAX_V1 262144
#define SOSIX_DARWIN_SANDBOX_ERROR_MAX_V1 512

SplArray* sosix_darwin_sandbox_apply_profile_v1(SplArray* profile);

SplArray* sosix_darwin_sandbox_apply_profile_v1(SplArray* profile) {
    const int64_t count = 2 + SOSIX_DARWIN_SANDBOX_ERROR_MAX_V1;
    SplArray* answer = rt_array_new(count);
    if (!answer) return NULL;
    for (int64_t i = 0; i < count; i++) if (!rt_array_push(answer, rt_value_int(0))) {
        rt_array_free(answer); return NULL;
    }
#if defined(__APPLE__)
    int64_t length = profile ? rt_array_len(profile) : -1;
    if (length < 1 || length > SOSIX_DARWIN_SANDBOX_PROFILE_MAX_V1) {
        (void)rt_array_set(answer, 0, rt_value_int(-1)); return answer;
    }
    char* text = malloc((size_t)length + 1);
    if (!text) { (void)rt_array_set(answer, 0, rt_value_int(-6)); return answer; }
    for (int64_t i = 0; i < length; i++) {
        int64_t value = rt_array_get(profile, i);
        /* NUL would silently truncate the policy the caller compiled. */
        if (!rt_value_is_int(value) || rt_value_as_int(value) < 1 || rt_value_as_int(value) > 255) {
            free(text); (void)rt_array_set(answer, 0, rt_value_int(-1)); return answer;
        }
        text[i] = (char)rt_value_as_int(value);
    }
    text[length] = 0;
    char* error = NULL;
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
    int rc = sandbox_init(text, 0, &error);
#pragma clang diagnostic pop
    free(text);
    int64_t copied = 0;
    if (rc != 0 && error) {
        while (copied < SOSIX_DARWIN_SANDBOX_ERROR_MAX_V1 && error[copied]) {
            (void)rt_array_set(answer, 2 + copied, rt_value_int((unsigned char)error[copied]));
            copied++;
        }
    }
    if (error) {
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
        sandbox_free_error(error);
#pragma clang diagnostic pop
    }
    /* rc==0 means the kernel applied the profile; it is reported as applied
     * even if an (unexpected) error buffer accompanied it, because claiming a
     * refusal for an already-confined process would be false. */
    (void)rt_array_set(answer, 0, rt_value_int(rc == 0 ? 0 : -3));
    (void)rt_array_set(answer, 1, rt_value_int(copied));
#else
    (void)profile;
    (void)rt_array_set(answer, 0, rt_value_int(-4));
#endif
    return answer;
}
#endif
