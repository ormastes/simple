/*
 * Platform dispatcher — picks the correct platform header.
 */
#ifndef SPL_PLATFORM_H
#define SPL_PLATFORM_H

#if defined(_WIN32)
#  include "platform_win.h"
#elif defined(__APPLE__)
#  include "platform_macos.h"
#elif defined(__FreeBSD__)
#  include "platform_freebsd.h"
#elif defined(__OpenBSD__)
#  include "platform_openbsd.h"
#elif defined(__NetBSD__)
#  include "platform_netbsd.h"
#elif defined(__linux__)
#  include "platform_linux.h"
#else
#  include "platform_linux.h"
#endif

#endif /* SPL_PLATFORM_H */
