/*
 * FreeBSD platform header — defines __BSD_VISIBLE before POSIX includes.
 */
#ifndef SPL_PLATFORM_FREEBSD_H
#define SPL_PLATFORM_FREEBSD_H

#ifndef __BSD_VISIBLE
#define __BSD_VISIBLE 1
#endif

#include "unix_common.h"

#endif /* SPL_PLATFORM_FREEBSD_H */
