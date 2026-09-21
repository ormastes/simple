/* Native Windows behaviour harness for the D3D11 event-query receipt ABI. */
#include <stdint.h>
#include <windows.h>

int64_t rt_directx_submission_submit(int64_t width, int64_t height, const int64_t *words, int64_t words_len);
int64_t rt_directx_submission_poll(int64_t submission_id);
int64_t rt_directx_submission_complete(int64_t submission_id);
int64_t rt_directx_submission_retire(int64_t submission_id);
int64_t rt_directx_submission_readback_pixel(int64_t submission_id);

int main(void) {
    /* Header + one CLEAR record, the smallest accepted real D3D11 workload. */
    const int64_t words[] = {
        0x44583131, 1, 1, 12,
        1, 8, 0, 0, 0, 0, 0xff102030, 0
    };
    int64_t submission = rt_directx_submission_submit(1, 1, words, 12);
    const int64_t invalid_words[] = { 0, 1, 1, 12, 1, 8, 0, 0, 0, 0, 0xff102030, 0 };
    int64_t phase;
    int retries = 2000;
    if (submission <= 0) return 10;
    if (rt_directx_submission_submit(1, 1, invalid_words, 12) != 0) return 16;
    phase = rt_directx_submission_poll(submission);
    if (phase != 1 && phase != 2) return 11;
    while (phase == 1 && retries-- > 0) {
        Sleep(1);
        phase = rt_directx_submission_poll(submission);
    }
    if (phase != 2) return 12;
    if (rt_directx_submission_readback_pixel(submission) != 0xff102030) return 17;
    if (rt_directx_submission_complete(submission) != 3) return 13;
    if (rt_directx_submission_retire(submission) != 4) return 14;
    return 0;
}
