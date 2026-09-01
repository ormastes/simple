#define _GNU_SOURCE
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

int64_t rt_cache_host_open_root_v1(const uint8_t *, int64_t);
int64_t rt_cache_host_close_v1(int64_t);
int64_t rt_cache_host_authenticate_peer_v1(int64_t, int64_t);
int64_t rt_cache_host_acquire_exclusive_lock_v1(int64_t, int64_t);
int64_t rt_cache_host_boot_identity_v1(int64_t);
int64_t rt_cache_host_advance_writer_epoch_v1(int64_t, int64_t);
int64_t rt_cache_host_publish_readiness_v1(int64_t, int64_t, const uint8_t *, int64_t);
int64_t rt_cache_host_validate_readiness_v1(int64_t, int64_t, const uint8_t *, int64_t, int64_t);
int64_t rt_cache_host_release_daemon_receipt_v1(int64_t);

int main(void) {
    char path[] = "/tmp/simple-daemon-authority-XXXXXX";
    assert(mkdtemp(path));
    int64_t root = rt_cache_host_open_root_v1((const uint8_t *)path, strlen(path));
    int sockets[2]; assert(socketpair(AF_UNIX, SOCK_STREAM, 0, sockets) == 0);
    int64_t peer = rt_cache_host_authenticate_peer_v1(root, sockets[0]); assert(peer > 0);
    int64_t lock = rt_cache_host_acquire_exclusive_lock_v1(root, peer); assert(lock > 0);
    assert(rt_cache_host_acquire_exclusive_lock_v1(root, peer) < 0);
    int64_t boot = rt_cache_host_boot_identity_v1(lock); assert(boot > 0);
    int64_t epoch = rt_cache_host_advance_writer_epoch_v1(lock, boot); assert(epoch > 0);
    const uint8_t nonce[] = "0123456789abcdef";
    int64_t ready = rt_cache_host_publish_readiness_v1(lock, epoch, nonce, 16); assert(ready > 0);
    assert(rt_cache_host_validate_readiness_v1(peer, ready, nonce, 16, epoch) == 1);
    assert(rt_cache_host_validate_readiness_v1(peer, ready, (const uint8_t *)"fedcba9876543210", 16, epoch) < 0);
    assert(rt_cache_host_release_daemon_receipt_v1(lock) == 0);
    assert(rt_cache_host_release_daemon_receipt_v1(peer) == 0);
    assert(rt_cache_host_release_daemon_receipt_v1(boot) == 0);
    close(sockets[0]); close(sockets[1]); rt_cache_host_close_v1(root);
    unlink(path); rmdir(path);
    return 0;
}
