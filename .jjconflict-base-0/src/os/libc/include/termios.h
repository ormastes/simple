/*
 * SimpleOS <termios.h> — POSIX terminal control
 *
 * NOTE on kernel wiring (see doc/03_plan/os/simpleos/host_os_completeness_plan.md H3):
 * SimpleOS's TTY/line-discipline state lives in a userspace ECS service,
 * os.kernel.services.tty_service (src/os/services/tty_service.spl), with
 * its own Termios{iflag,oflag,lflag,cc} component and ISIG/ICANON/ECHO
 * bit layout. As of this header there is NO syscall dispatch entry that
 * lets a ring-3 process reach that service: src/os/kernel/ipc/syscall.spl
 * has no "case NN: # TtyGetAttr/TtySetAttr" arm, and neither does the
 * strong-override shim layer in src/os/kernel/abi/syscall_shim*.spl (the
 * network syscalls 70-77 and file syscalls 30-48/57-69 are the highest
 * allocated blocks; the next free id would need to be picked above 99,
 * or a gap reused, by whoever owns src/os/kernel/ipc/syscall.spl's ID
 * space next). Adding that syscall is explicitly OUT OF SCOPE for this
 * lane (Lane H3) — see the guide's "do not invent a kernel tty syscall
 * layer in this lane" constraint. tcgetattr()/tcsetattr() therefore
 * fail closed with ENOSYS below; cfmakeraw()/cfget*speed()/cfset*speed()
 * are pure struct transforms with no kernel dependency and are fully
 * implemented.
 *
 * struct termios field layout follows the POSIX-required member set
 * (c_iflag/c_oflag/c_cflag/c_lflag/c_cc/c_ispeed/c_ospeed); flag bit
 * values for ISIG/ICANON/ECHO intentionally match
 * src/os/services/tty_service.spl's Termios lflag constants (ISIG=1,
 * ICANON=2, ECHO=8) and VINTR/VERASE/VKILL/VEOF cc[] indices (0/2/3/4)
 * so that a future syscall implementation can pass this struct through
 * with no bit-remapping.
 */

#ifndef _SIMPLEOS_TERMIOS_H
#define _SIMPLEOS_TERMIOS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned int tcflag_t;
typedef unsigned char cc_t;
typedef unsigned int speed_t;

#define NCCS 32

/* c_cc[] indices. Values 0/2/3/4 match tty_service.spl's
 * VINTR/VERASE/VKILL/VEOF; the remaining POSIX-named indices are
 * reserved slots with no SimpleOS backend behavior yet. */
#define VINTR    0
#define VQUIT    1
#define VERASE   2
#define VKILL    3
#define VEOF     4
#define VTIME    5
#define VMIN     6
#define VSTART   8
#define VSTOP    9
#define VSUSP    10
#define VEOL     11

/* c_iflag bits */
#define BRKINT  0x0001
#define ICRNL   0x0002
#define IGNBRK  0x0004
#define IGNCR   0x0008
#define IGNPAR  0x0010
#define INLCR   0x0020
#define INPCK   0x0040
#define ISTRIP  0x0080
#define IXOFF   0x0100
#define IXON    0x0200
#define PARMRK  0x0400

/* c_oflag bits */
#define OPOST   0x0001
#define ONLCR   0x0002

/* c_cflag bits */
#define CS8     0x0030
#define CREAD   0x0080
#define CLOCAL  0x0800

/* c_lflag bits — ISIG/ICANON/ECHO numeric values match
 * tty_service.spl's Termios.lflag constants exactly. */
#define ISIG    0x0001
#define ICANON  0x0002
#define ECHO    0x0008
#define ECHOE   0x0010
#define ECHOK   0x0020
#define ECHONL  0x0040
#define IEXTEN  0x0100
#define NOFLSH  0x0200
#define TOSTOP  0x0400

/* tcsetattr() "optional_actions" */
#define TCSANOW   0
#define TCSADRAIN 1
#define TCSAFLUSH 2

/* tcflush() queue selector */
#define TCIFLUSH  0
#define TCOFLUSH  1
#define TCIOFLUSH 2

/* tcflow() action */
#define TCOOFF 0
#define TCOON  1
#define TCIOFF 2
#define TCION  3

/* Baud rate symbols (values are opaque tokens, not literal bps) */
#define B0     0
#define B9600  13
#define B19200 14
#define B38400 15
#define B115200 4098

struct termios {
    tcflag_t c_iflag;
    tcflag_t c_oflag;
    tcflag_t c_cflag;
    tcflag_t c_lflag;
    cc_t     c_cc[NCCS];
    speed_t  c_ispeed;
    speed_t  c_ospeed;
};

/* tcgetattr()/tcsetattr(): SimpleOS has no kernel syscall path to the
 * TTY service yet (see file header note) — both fail closed with
 * ENOSYS, matching the "never fake success" fail-closed rule. */
int tcgetattr(int fd, struct termios *termios_p);
int tcsetattr(int fd, int optional_actions, const struct termios *termios_p);

/* tcflush()/tcdrain()/tcsendbreak()/tcflow() would also require the
 * kernel TTY syscall path; ENOSYS for the same reason. */
int tcflush(int fd, int queue_selector);
int tcdrain(int fd);
int tcsendbreak(int fd, int duration);
int tcflow(int fd, int action);

/* Pure struct transforms — no kernel dependency, fully implemented. */
void cfmakeraw(struct termios *termios_p);
speed_t cfgetispeed(const struct termios *termios_p);
speed_t cfgetospeed(const struct termios *termios_p);
int cfsetispeed(struct termios *termios_p, speed_t speed);
int cfsetospeed(struct termios *termios_p, speed_t speed);
int cfsetspeed(struct termios *termios_p, speed_t speed);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_TERMIOS_H */
