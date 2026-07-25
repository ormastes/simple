/*
 * SimpleOS Terminal Control (termios)
 *
 * See include/termios.h for the "why ENOSYS" note: no kernel syscall
 * dispatch reaches os.kernel.services.tty_service yet (verified against
 * src/os/kernel/ipc/syscall.spl and src/os/kernel/abi/syscall_shim*.spl —
 * neither has a Tty* syscall id). tcgetattr()/tcsetattr()/tcflush()/
 * tcdrain()/tcsendbreak()/tcflow() therefore fail closed with ENOSYS
 * rather than silently no-op-succeeding. cfmakeraw() and the speed
 * accessors are pure struct transforms with no kernel dependency and
 * are fully implemented below.
 */

#include "include/termios.h"
#include "include/errno.h"
#include "include/string.h"

extern int errno;

int tcgetattr(int fd, struct termios *termios_p) {
    (void)fd; (void)termios_p;
    errno = ENOSYS;
    return -1;
}

int tcsetattr(int fd, int optional_actions, const struct termios *termios_p) {
    (void)fd; (void)optional_actions; (void)termios_p;
    errno = ENOSYS;
    return -1;
}

int tcflush(int fd, int queue_selector) {
    (void)fd; (void)queue_selector;
    errno = ENOSYS;
    return -1;
}

int tcdrain(int fd) {
    (void)fd;
    errno = ENOSYS;
    return -1;
}

int tcsendbreak(int fd, int duration) {
    (void)fd; (void)duration;
    errno = ENOSYS;
    return -1;
}

int tcflow(int fd, int action) {
    (void)fd; (void)action;
    errno = ENOSYS;
    return -1;
}

void cfmakeraw(struct termios *termios_p) {
    if (!termios_p) return;
    termios_p->c_iflag &= ~(unsigned)(BRKINT | ICRNL | IGNBRK | IGNCR |
                                       INLCR | INPCK | ISTRIP | IXON);
    termios_p->c_oflag &= ~(unsigned)OPOST;
    termios_p->c_lflag &= ~(unsigned)(ECHO | ECHONL | ICANON | IEXTEN | ISIG);
    termios_p->c_cflag &= ~(unsigned)CS8;
    termios_p->c_cflag |= CS8;
    termios_p->c_cc[VMIN] = 1;
    termios_p->c_cc[VTIME] = 0;
}

speed_t cfgetispeed(const struct termios *termios_p) {
    return termios_p ? termios_p->c_ispeed : 0;
}

speed_t cfgetospeed(const struct termios *termios_p) {
    return termios_p ? termios_p->c_ospeed : 0;
}

int cfsetispeed(struct termios *termios_p, speed_t speed) {
    if (!termios_p) { errno = EINVAL; return -1; }
    termios_p->c_ispeed = speed;
    return 0;
}

int cfsetospeed(struct termios *termios_p, speed_t speed) {
    if (!termios_p) { errno = EINVAL; return -1; }
    termios_p->c_ospeed = speed;
    return 0;
}

int cfsetspeed(struct termios *termios_p, speed_t speed) {
    if (!termios_p) { errno = EINVAL; return -1; }
    termios_p->c_ispeed = speed;
    termios_p->c_ospeed = speed;
    return 0;
}
