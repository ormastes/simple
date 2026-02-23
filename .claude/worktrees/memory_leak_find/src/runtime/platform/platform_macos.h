/*
 * macOS platform header — defines _DARWIN_C_SOURCE before POSIX includes.
 */
#ifndef SPL_PLATFORM_MACOS_H
#define SPL_PLATFORM_MACOS_H

#ifndef _DARWIN_C_SOURCE
#define _DARWIN_C_SOURCE
#endif

#include "unix_common.h"

#endif /* SPL_PLATFORM_MACOS_H */
