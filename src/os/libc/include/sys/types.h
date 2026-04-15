/*
 * SimpleOS <sys/types.h> — POSIX type definitions
 */

#ifndef _SIMPLEOS_SYS_TYPES_H
#define _SIMPLEOS_SYS_TYPES_H

#ifdef __cplusplus
extern "C" {
#endif

/* Fixed-width types from compiler */
#include <stdint.h>
#include <stddef.h>

/* Process / user / group IDs */
typedef int32_t  pid_t;
typedef uint32_t uid_t;
typedef uint32_t gid_t;

/* File system types */
typedef uint32_t mode_t;
typedef int64_t  off_t;
typedef int64_t  ssize_t;
typedef int64_t  time_t;
typedef int32_t  clockid_t;
typedef uint64_t dev_t;
typedef uint64_t ino_t;
typedef uint64_t nlink_t;
typedef int64_t  blkcnt_t;
typedef int64_t  blksize_t;

/* Misc POSIX types */
typedef uint32_t useconds_t;
typedef int64_t  suseconds_t;

/* pthread types — opaque structures */
typedef unsigned long pthread_t;

typedef struct {
    unsigned char __data[40];
} pthread_mutex_t;

typedef struct {
    unsigned char __data[48];
} pthread_cond_t;

typedef unsigned int pthread_key_t;

typedef int pthread_once_t;

typedef struct {
    unsigned char __data[56];
} pthread_attr_t;

typedef struct {
    unsigned char __data[8];
} pthread_mutexattr_t;

typedef struct {
    unsigned char __data[8];
} pthread_condattr_t;

/* Signal set — 64-bit bitmask */
typedef struct {
    unsigned long __bits[1];
} sigset_t;

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_SYS_TYPES_H */
