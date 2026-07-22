/* openocd_bitbang_glue.c — GHDL VHPIDIRECT socket glue for the OpenOCD
 * remote_bitbang driver (Stage 5).
 *
 * tb_openocd_bitbang.vhd binds these three functions with
 * `attribute foreign ... "VHPIDIRECT ..."`:
 *   bb_init(port) — listen on 127.0.0.1:<port>, block until OpenOCD connects.
 *   bb_next()     — blocking read of the next protocol byte (-1 on EOF).
 *   bb_send(bit)  — send '0'/'1' in answer to an 'R' (read TDO) request.
 *
 * Build (ghdl-mcode backend — resolves the "VHPIDIRECT bb_glue.so <sym>"
 * foreign strings via dlopen, so build a shared lib and put it on
 * LD_LIBRARY_PATH):
 *   cc -shared -fPIC -o bb_glue.so openocd_bitbang_glue.c
 * (With a gcc/llvm GHDL backend, `cc -c` + `ghdl -e -Wl,<obj>` also works
 * if the foreign strings are shortened to "VHPIDIRECT <sym>".)
 *
 * Simulation-only harness glue; never synthesized, never linked into any
 * product binary.
 */

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>

static int listen_fd = -1;
static int conn_fd = -1;

int bb_init(int port)
{
  struct sockaddr_in a;
  int one = 1;

  listen_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (listen_fd < 0)
    return -1;
  setsockopt(listen_fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  memset(&a, 0, sizeof a);
  a.sin_family = AF_INET;
  a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  a.sin_port = htons((unsigned short)port);
  if (bind(listen_fd, (struct sockaddr *)&a, sizeof a) < 0)
    return -2;
  if (listen(listen_fd, 1) < 0)
    return -3;
  fprintf(stderr, "[bitbang] listening on 127.0.0.1:%d, waiting for OpenOCD\n",
          port);
  conn_fd = accept(listen_fd, NULL, NULL);
  if (conn_fd < 0)
    return -4;
  setsockopt(conn_fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
  fprintf(stderr, "[bitbang] OpenOCD connected\n");
  return 0;
}

int bb_next(void)
{
  unsigned char c;
  ssize_t n = read(conn_fd, &c, 1);
  if (n <= 0)
    return -1;
  return (int)c;
}

void bb_send(int bit)
{
  char c = bit ? '1' : '0';
  ssize_t n = write(conn_fd, &c, 1);
  (void)n;
}
