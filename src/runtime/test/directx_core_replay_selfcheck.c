/* Selfcheck for runtime_directx_core.c command replay (clear/rect/image).
 * Skips (exit 0) when no D3D11 hardware device is available or off Windows.
 * Build (llvm-mingw): clang -I src/runtime src/runtime/test/directx_core_replay_selfcheck.c
 *   src/runtime/runtime_directx_core.c -ld3d11 -ldxgi; on other hosts link without the libs. */
#include <stdint.h>
#include <stdio.h>

int64_t rt_directx_execute_readback_checked(int64_t width, int64_t height,
                                            const int64_t *words, int64_t words_len,
                                            uint32_t *out, int64_t out_len);
int64_t rt_directx_hardware_adapter_identity(void);

int main(void) {
    /* 4x4: clear red, green rect (1,1,2,2), blue 1x1 image at (3,3). */
    int64_t words[4 + 8 + 8 + 9] = {
        0x44583131, 1, 3, 29,
        1, 8, 0, 0, 0, 0, 0xffff0000, 0,
        2, 8, 1, 1, 2, 2, 0xff00ff00, 0,
        3, 9, 3, 3, 1, 1, 0, 1, 0xff0000ff,
    };
    uint32_t out[2 + 16] = {0};
    int fails = 0;
    if (rt_directx_hardware_adapter_identity() == 0) {
        printf("SKIP directx_core_replay_selfcheck: no D3D11 hardware device\n");
        return 0;
    }
    if (rt_directx_execute_readback_checked(4, 4, words, 29, out, 18) <= 0) {
        printf("FAIL readback returned 0\n");
        return 1;
    }
#define PX(x, y) out[2 + (y) * 4 + (x)]
    if (PX(0, 0) != 0xffff0000u) { printf("FAIL clear %08x\n", PX(0, 0)); fails++; }
    if (PX(1, 1) != 0xff00ff00u || PX(2, 2) != 0xff00ff00u) { printf("FAIL rect %08x\n", PX(1, 1)); fails++; }
    if (PX(3, 3) != 0xff0000ffu) { printf("FAIL image %08x\n", PX(3, 3)); fails++; }
    /* malformed stream (bad total_words) must be rejected */
    words[3] = 28;
    if (rt_directx_execute_readback_checked(4, 4, words, 29, out, 18) != 0) { printf("FAIL bad stream accepted\n"); fails++; }
    if (fails) return 1;
    printf("PASS directx_core_replay_selfcheck\n");
    return 0;
}
