#include "runtime.h"

#include <stdint.h>

#define SIMPLEOS_SYSCALL_EINVAL (-22)
#define SIMPLEOS_SYSCALL_ENOMEM (-12)
#define SIMPLEOS_SYSCALL_EOVERFLOW (-75)
#define SIMPLEOS_SYSCALL_MAX_PATH 4096u
#define SIMPLEOS_SYSCALL_SOCKADDR_BYTES 16u
#define SIMPLEOS_SYSCALL_MAX_IO_BYTES (1024u * 1024u)

extern int64_t simpleos_syscall(uint64_t id, uint64_t arg0, uint64_t arg1,
                                uint64_t arg2, uint64_t arg3, uint64_t arg4);

static int64_t array_length(int64_t value) {
    int64_t length = rt_array_bytes_validate(value);
    if (length < 0) return SIMPLEOS_SYSCALL_EINVAL;
    if ((uint64_t)length > SIMPLEOS_SYSCALL_MAX_IO_BYTES) {
        return SIMPLEOS_SYSCALL_EOVERFLOW;
    }
    return length;
}

static uint8_t *materialize_bytes(int64_t value, int64_t length) {
    if (length == 0) return (uint8_t *)rt_alloc(1);
    uint8_t *bytes = (uint8_t *)rt_alloc(length);
    if (!bytes) return NULL;
    if (rt_array_bytes_copy_checked(value, bytes, length) != length) {
        rt_free(bytes);
        return NULL;
    }
    return bytes;
}

static int copy_back_bytes(int64_t value, const uint8_t *bytes, int64_t length) {
    return rt_array_bytes_store_checked(value, bytes, length) == length;
}

static int64_t syscall_input(uint64_t id, uint64_t fd, int64_t value) {
    int64_t length = array_length(value);
    if (length < 0) return length;
    uint8_t *bytes = materialize_bytes(value, length);
    if (!bytes) return SIMPLEOS_SYSCALL_ENOMEM;
    int64_t result = simpleos_syscall(
        id, fd, (uint64_t)(uintptr_t)bytes, (uint64_t)length, 0, 0);
    rt_free(bytes);
    return result;
}

static int64_t syscall_output(
    uint64_t id, uint64_t fd, int64_t value, uint64_t max_len) {
    int64_t capacity = array_length(value);
    if (capacity < 0) return capacity;
    if (max_len > (uint64_t)capacity || max_len > SIMPLEOS_SYSCALL_MAX_IO_BYTES) {
        return SIMPLEOS_SYSCALL_EINVAL;
    }
    uint8_t *bytes = (uint8_t *)rt_alloc(max_len == 0 ? 1 : (int64_t)max_len);
    if (!bytes) return SIMPLEOS_SYSCALL_ENOMEM;
    int64_t result = simpleos_syscall(
        id, fd, (uint64_t)(uintptr_t)bytes, max_len, 0, 0);
    if (result > 0) {
        if ((uint64_t)result > max_len ||
            !copy_back_bytes(value, bytes, result)) {
            result = SIMPLEOS_SYSCALL_EOVERFLOW;
        }
    }
    rt_free(bytes);
    return result;
}

int64_t rt_simpleos_file_open_bytes(int64_t path, uint64_t flags) {
    int64_t length = array_length(path);
    if (length <= 0 || (uint64_t)length > SIMPLEOS_SYSCALL_MAX_PATH) {
        return SIMPLEOS_SYSCALL_EINVAL;
    }
    uint8_t *bytes = materialize_bytes(path, length);
    if (!bytes) return SIMPLEOS_SYSCALL_ENOMEM;
    int64_t result = simpleos_syscall(
        30, (uint64_t)(uintptr_t)bytes, (uint64_t)length, flags, 0, 0);
    rt_free(bytes);
    return result;
}

int64_t rt_simpleos_file_read_bytes(uint64_t fd, int64_t out, uint64_t max_len) {
    return syscall_output(31, fd, out, max_len);
}

int64_t rt_simpleos_file_write_bytes(uint64_t fd, int64_t data) {
    return syscall_input(32, fd, data);
}

int64_t rt_simpleos_file_rename_bytes(int64_t old_path, int64_t new_path) {
    int64_t old_len = array_length(old_path);
    int64_t new_len = array_length(new_path);
    if (old_len <= 0 || new_len <= 0 ||
        (uint64_t)old_len > SIMPLEOS_SYSCALL_MAX_PATH ||
        (uint64_t)new_len > SIMPLEOS_SYSCALL_MAX_PATH) {
        return SIMPLEOS_SYSCALL_EINVAL;
    }
    uint8_t *old_bytes = materialize_bytes(old_path, old_len);
    if (!old_bytes) return SIMPLEOS_SYSCALL_ENOMEM;
    uint8_t *new_bytes = materialize_bytes(new_path, new_len);
    if (!new_bytes) {
        rt_free(old_bytes);
        return SIMPLEOS_SYSCALL_ENOMEM;
    }
    int64_t result = simpleos_syscall(
        44, (uint64_t)(uintptr_t)old_bytes, (uint64_t)old_len,
        (uint64_t)(uintptr_t)new_bytes, (uint64_t)new_len, 0);
    rt_free(new_bytes);
    rt_free(old_bytes);
    return result;
}

int64_t rt_simpleos_socket_bind_bytes(uint64_t fd, int64_t sockaddr) {
    if (array_length(sockaddr) != SIMPLEOS_SYSCALL_SOCKADDR_BYTES) {
        return SIMPLEOS_SYSCALL_EINVAL;
    }
    return syscall_input(71, fd, sockaddr);
}

int64_t rt_simpleos_socket_connect_bytes(uint64_t fd, int64_t sockaddr) {
    if (array_length(sockaddr) != SIMPLEOS_SYSCALL_SOCKADDR_BYTES) {
        return SIMPLEOS_SYSCALL_EINVAL;
    }
    return syscall_input(73, fd, sockaddr);
}

int64_t rt_simpleos_socket_send_bytes(uint64_t fd, int64_t data) {
    return syscall_input(75, fd, data);
}

int64_t rt_simpleos_socket_recv_bytes(uint64_t fd, int64_t out, uint64_t max_len) {
    return syscall_output(76, fd, out, max_len);
}
