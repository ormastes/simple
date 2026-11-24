/* runtime_file_stat_impl.h -- private no-shell stat probes shared by
 * runtime.c and runtime_native.c.
 *
 * Not a public header: include it exactly once, from one translation unit,
 * after RT_TEXT_PATH_MAX / rt_text_arg_to_path are defined and, on _WIN32,
 * after platform/runtime_win_long_path.h (rt_widen_long_path_rc). Everything
 * here is static; the exported rt_file_is_regular_no_follow and
 * rt_file_is_char_device stay hand-written in each includer as one-line
 * wrappers, so each lane keeps its own linkage. */
#ifndef SIMPLE_RUNTIME_FILE_STAT_IMPL_H
#define SIMPLE_RUNTIME_FILE_STAT_IMPL_H

static bool rt_file_is_regular_no_follow_impl(const uint8_t* path_ptr, uint64_t path_len) {
    char path_buf[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(path_ptr, path_len, path_buf, sizeof(path_buf))) return 0;
    const char* path = path_buf;
#if defined(_WIN32)
    if (!path) return 0;
    /* Long-path widened, like rt_file_read_regular_no_follow_bounded: the
     * plain UTF-16 conversion failed past MAX_PATH, so a long
     * package-module index path read as "not a regular file" and admission
     * failed package-index:generation-unavailable (2026-09-25). */
    wchar_t* wide_path = rt_widen_long_path_rc(path);
    if (!wide_path) return 0;
    DWORD attributes = GetFileAttributesW(wide_path);
    free(wide_path);
    return attributes != INVALID_FILE_ATTRIBUTES &&
           (attributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT)) == 0;
#else
    struct stat st;
    return path && lstat(path, &st) == 0 && S_ISREG(st.st_mode);
#endif
}

/* rt_file_is_char_device: no-shell stat(2) probe for whether `path` is a
 * character device (e.g. a DRM render node). Added so callers like
 * os.compositor.vulkan_compositor_backend's detect_virtio_gpu_device() can
 * drop their `/bin/sh -c "test -c '...'"` shell-out entirely -- see
 * doc/08_tracking/bug/vulkan_detect_virtio_gpu_device_is_existence_check_not_device_probe_2026-08-07.md.
 * Symlinks are followed (stat, not lstat): the caller wants to know whether
 * the path ultimately resolves to a character device, not whether the leaf
 * entry itself is one. */
static int rt_file_is_char_device_impl(const uint8_t* path_ptr, uint64_t path_len) {
#if defined(_WIN32)
    (void)path_ptr; (void)path_len;
    return 0;
#else
    /* The compiler emits the two-argument (ptr, len) form for `text` externs
     * (runtime_sffi.rs / src/compiler/50.mir/text_extern_abi.spl); a Simple
     * `text` is NOT NUL-terminated, so the buffer must be copied. */
    char buf[4096];
    if (!path_ptr || path_len >= sizeof(buf)) return 0;
    memcpy(buf, path_ptr, (size_t)path_len);
    buf[(size_t)path_len] = '\0';
    struct stat st;
    return stat(buf, &st) == 0 && S_ISCHR(st.st_mode);
#endif
}

#endif /* SIMPLE_RUNTIME_FILE_STAT_IMPL_H */
