/* Minimal native DirectX 11 capsule for the core-C runtime lane. */

#include <stdint.h>
#include <stddef.h>

#if defined(_WIN32)

#define COBJMACROS
#define INITGUID
#include <windows.h>
#include <d3d11_1.h>
#include <dxgi.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define RT_DX11_MAGIC 0x44583131u
#define RT_DX11_VERSION 1u
#define RT_DX11_OP_CLEAR 1u
#define RT_DX11_OP_RECT 2u
#define RT_DX11_OP_IMAGE 3u
#define RT_DX11_RECORD_WORDS 8u

typedef struct RtDirectXDevice {
    ID3D11Device *device;
    ID3D11DeviceContext *context;
    ID3D11DeviceContext1 *context1;
    int64_t identity;
} RtDirectXDevice;

/* A submission owns its D3D11 device/context until retirement.  Its event
 * query is the only source of the gpu_finished transition; creating it never
 * changes phase.  Records remain as tombstones after retirement so an old
 * scheduler receipt cannot alias a later submission. */
typedef struct RtDirectXSubmission {
    int64_t id;
    int phase;
    RtDirectXDevice device;
    ID3D11Texture2D *target;
    ID3D11RenderTargetView *view;
    ID3D11Texture2D *staging;
    ID3D11Query *event_query;
    struct RtDirectXSubmission *next;
} RtDirectXSubmission;

#define RT_DX11_SUBMISSION_SUBMITTED 1
#define RT_DX11_SUBMISSION_GPU_FINISHED 2
#define RT_DX11_SUBMISSION_COMPLETED 3
#define RT_DX11_SUBMISSION_RETIRED 4

static INIT_ONCE rt_directx_lock_once = INIT_ONCE_STATIC_INIT;
static CRITICAL_SECTION rt_directx_lock;
static RtDirectXSubmission *rt_directx_submissions;
static int64_t rt_directx_next_submission_id = 1;
/* Bounded retired-ID cache lets stale scheduler receipt copies converge to a
 * terminal phase without retaining COM resources or an unbounded node list. */
#define RT_DX11_RETIRED_ID_CACHE 256
static int64_t rt_directx_retired_ids[RT_DX11_RETIRED_ID_CACHE];
static uint32_t rt_directx_retired_cursor;

static BOOL CALLBACK rt_directx_init_lock(PINIT_ONCE once, PVOID parameter, PVOID *context) {
    (void)once;
    (void)parameter;
    (void)context;
    InitializeCriticalSection(&rt_directx_lock);
    return TRUE;
}

static int rt_directx_enter(void) {
    if (!InitOnceExecuteOnce(&rt_directx_lock_once, rt_directx_init_lock, NULL, NULL)) return 0;
    EnterCriticalSection(&rt_directx_lock);
    return 1;
}

static void rt_directx_leave(void) {
    LeaveCriticalSection(&rt_directx_lock);
}

static uint64_t rt_directx_hash_u32(uint64_t hash, uint32_t value) {
    hash ^= value;
    return hash * UINT64_C(1099511628211);
}

static int64_t rt_directx_adapter_identity(ID3D11Device *device) {
    IDXGIDevice *dxgi_device = NULL;
    IDXGIAdapter *adapter = NULL;
    DXGI_ADAPTER_DESC desc;
    uint64_t hash = UINT64_C(1469598103934665603);
    HRESULT hr;

    memset(&desc, 0, sizeof(desc));
    hr = ID3D11Device_QueryInterface(device, &IID_IDXGIDevice, (void **)&dxgi_device);
    if (FAILED(hr) || !dxgi_device) goto fail;
    hr = IDXGIDevice_GetAdapter(dxgi_device, &adapter);
    if (FAILED(hr) || !adapter) goto fail;
    hr = IDXGIAdapter_GetDesc(adapter, &desc);
    if (FAILED(hr)) goto fail;

    /* D3D_DRIVER_TYPE_HARDWARE already excludes WARP; reject Microsoft's
       software/basic adapter identifiers as an additional fail-closed gate. */
    if (desc.VendorId == 0x1414u && (desc.DeviceId == 0x008cu || desc.DeviceId == 0x008du)) goto fail;

    hash = rt_directx_hash_u32(hash, desc.VendorId);
    hash = rt_directx_hash_u32(hash, desc.DeviceId);
    hash = rt_directx_hash_u32(hash, desc.SubSysId);
    hash = rt_directx_hash_u32(hash, desc.Revision);
    hash = rt_directx_hash_u32(hash, desc.AdapterLuid.LowPart);
    hash = rt_directx_hash_u32(hash, (uint32_t)desc.AdapterLuid.HighPart);
    hash &= ((uint64_t)INT64_MAX >> 3);
    if (hash == 0) hash = 1;

    IDXGIAdapter_Release(adapter);
    IDXGIDevice_Release(dxgi_device);
    return (int64_t)hash;

fail:
    if (adapter) IDXGIAdapter_Release(adapter);
    if (dxgi_device) IDXGIDevice_Release(dxgi_device);
    return 0;
}

static void rt_directx_close_device(RtDirectXDevice *state) {
    if (state->context1) ID3D11DeviceContext1_Release(state->context1);
    if (state->context) ID3D11DeviceContext_Release(state->context);
    if (state->device) ID3D11Device_Release(state->device);
    memset(state, 0, sizeof(*state));
}

static RtDirectXSubmission *rt_directx_submission_find(int64_t id) {
    RtDirectXSubmission *current = rt_directx_submissions;
    while (current) {
        if (current->id == id) return current;
        current = current->next;
    }
    return NULL;
}

static int rt_directx_submission_was_retired(int64_t id) {
    uint32_t index;
    for (index = 0; index < RT_DX11_RETIRED_ID_CACHE; index++) {
        if (rt_directx_retired_ids[index] == id) return 1;
    }
    return 0;
}

static void rt_directx_submission_note_retired(int64_t id) {
    rt_directx_retired_ids[rt_directx_retired_cursor++ % RT_DX11_RETIRED_ID_CACHE] = id;
}

static void rt_directx_submission_release(RtDirectXSubmission *submission);

static void rt_directx_submission_unlink_and_free(RtDirectXSubmission *submission) {
    RtDirectXSubmission **link = &rt_directx_submissions;
    while (*link && *link != submission) link = &(*link)->next;
    if (*link == submission) *link = submission->next;
    rt_directx_submission_release(submission);
    free(submission);
}

static void rt_directx_submission_release(RtDirectXSubmission *submission) {
    if (submission->event_query) ID3D11Query_Release(submission->event_query);
    if (submission->staging) ID3D11Texture2D_Release(submission->staging);
    if (submission->view) ID3D11RenderTargetView_Release(submission->view);
    if (submission->target) ID3D11Texture2D_Release(submission->target);
    submission->event_query = NULL;
    submission->staging = NULL;
    submission->view = NULL;
    submission->target = NULL;
    rt_directx_close_device(&submission->device);
}

static int rt_directx_submission_poll_locked(RtDirectXSubmission *submission) {
    HRESULT hr;
    if (!submission) return -1;
    if (submission->phase != RT_DX11_SUBMISSION_SUBMITTED) return submission->phase;
    if (!submission->event_query || !submission->device.context) return -1;
    hr = ID3D11DeviceContext_GetData(submission->device.context, (ID3D11Asynchronous *)submission->event_query,
                                     NULL, 0, D3D11_ASYNC_GETDATA_DONOTFLUSH);
    if (hr == S_FALSE) return RT_DX11_SUBMISSION_SUBMITTED;
    if (FAILED(hr)) {
        rt_directx_submission_unlink_and_free(submission);
        return -1;
    }
    submission->phase = RT_DX11_SUBMISSION_GPU_FINISHED;
    return submission->phase;
}

static int rt_directx_open_device(RtDirectXDevice *state) {
    static const D3D_FEATURE_LEVEL levels[] = {
        D3D_FEATURE_LEVEL_11_1,
        D3D_FEATURE_LEVEL_11_0
    };
    D3D_FEATURE_LEVEL selected = (D3D_FEATURE_LEVEL)0;
    HRESULT hr;

    memset(state, 0, sizeof(*state));
    hr = D3D11CreateDevice(NULL, D3D_DRIVER_TYPE_HARDWARE, NULL,
                           D3D11_CREATE_DEVICE_BGRA_SUPPORT,
                           levels, 2, D3D11_SDK_VERSION,
                           &state->device, &selected, &state->context);
    if (hr == E_INVALIDARG) {
        hr = D3D11CreateDevice(NULL, D3D_DRIVER_TYPE_HARDWARE, NULL,
                               D3D11_CREATE_DEVICE_BGRA_SUPPORT,
                               &levels[1], 1, D3D11_SDK_VERSION,
                               &state->device, &selected, &state->context);
    }
    if (FAILED(hr) || !state->device || !state->context || selected < D3D_FEATURE_LEVEL_11_0) goto fail;
    hr = ID3D11DeviceContext_QueryInterface(state->context, &IID_ID3D11DeviceContext1,
                                             (void **)&state->context1);
    if (FAILED(hr) || !state->context1) goto fail;
    state->identity = rt_directx_adapter_identity(state->device);
    if (state->identity <= 0) goto fail;
    return 1;

fail:
    rt_directx_close_device(state);
    return 0;
}

static int rt_directx_word(const int64_t *words, int64_t index, uint32_t *out) {
    uint64_t value;
    if (!words || index < 0 || !out) return 0;
    value = (uint64_t)words[index];
    if ((value >> 32) != 0) return 0;
    *out = (uint32_t)value;
    return 1;
}

static int rt_directx_rect_valid(uint32_t x, uint32_t y, uint32_t w, uint32_t h,
                                 uint32_t width, uint32_t height) {
    return w > 0 && h > 0 && x <= width && y <= height && w <= width - x && h <= height - y;
}

static int rt_directx_stream_valid(uint32_t width, uint32_t height,
                                   const int64_t *words, int64_t words_len) {
    uint32_t magic, version, command_count, total_words;
    int64_t pos = 4;
    uint32_t command_index;

    if (!words || words_len < 4 || words_len > UINT32_MAX) return 0;
    if (width > UINT32_MAX / sizeof(uint32_t) ||
        (uint64_t)width * (uint64_t)height > SIZE_MAX / sizeof(uint32_t)) return 0;
    if (!rt_directx_word(words, 0, &magic) || magic != RT_DX11_MAGIC ||
        !rt_directx_word(words, 1, &version) || version != RT_DX11_VERSION ||
        !rt_directx_word(words, 2, &command_count) || command_count == 0 ||
        !rt_directx_word(words, 3, &total_words) || total_words != (uint32_t)words_len) return 0;
    if ((uint64_t)command_count > (uint64_t)(words_len - 4) / RT_DX11_RECORD_WORDS) return 0;

    for (command_index = 0; command_index < command_count; command_index++) {
        uint32_t op, record_words, x, y, w, h, arg, payload_words;
        uint64_t pixels;
        uint32_t pixel_index;
        if (words_len - pos < RT_DX11_RECORD_WORDS ||
            !rt_directx_word(words, pos + 0, &op) ||
            !rt_directx_word(words, pos + 1, &record_words) ||
            !rt_directx_word(words, pos + 2, &x) ||
            !rt_directx_word(words, pos + 3, &y) ||
            !rt_directx_word(words, pos + 4, &w) ||
            !rt_directx_word(words, pos + 5, &h) ||
            !rt_directx_word(words, pos + 6, &arg) ||
            !rt_directx_word(words, pos + 7, &payload_words)) return 0;
        if (record_words < RT_DX11_RECORD_WORDS || record_words != RT_DX11_RECORD_WORDS + payload_words ||
            (int64_t)record_words > words_len - pos) return 0;

        if (op == RT_DX11_OP_CLEAR) {
            if (record_words != RT_DX11_RECORD_WORDS || payload_words != 0 || x != 0 || y != 0 || w != 0 || h != 0) return 0;
        } else if (op == RT_DX11_OP_RECT) {
            if (record_words != RT_DX11_RECORD_WORDS || payload_words != 0 ||
                !rt_directx_rect_valid(x, y, w, h, width, height)) return 0;
            if (command_index == 0) return 0;
        } else if (op == RT_DX11_OP_IMAGE) {
            if (arg != 0 || !rt_directx_rect_valid(x, y, w, h, width, height)) return 0;
            pixels = (uint64_t)w * (uint64_t)h;
            if (pixels != payload_words) return 0;
            if (command_index == 0 && (x != 0 || y != 0 || w != width || h != height)) return 0;
            for (pixel_index = 0; pixel_index < payload_words; pixel_index++) {
                uint32_t pixel;
                if (!rt_directx_word(words, pos + RT_DX11_RECORD_WORDS + pixel_index, &pixel) ||
                    (pixel >> 24) != 0xffu) return 0;
            }
        } else {
            return 0;
        }
        pos += record_words;
    }
    return pos == words_len;
}

static void rt_directx_argb_color(uint32_t argb, float color[4]) {
    color[0] = (float)((argb >> 16) & 0xffu) / 255.0f;
    color[1] = (float)((argb >> 8) & 0xffu) / 255.0f;
    color[2] = (float)(argb & 0xffu) / 255.0f;
    color[3] = (float)((argb >> 24) & 0xffu) / 255.0f;
}

int64_t rt_directx_submission_submit(int64_t width_arg, int64_t height_arg,
                                     const int64_t *words, int64_t words_len) {
    RtDirectXSubmission *submission;
    D3D11_QUERY_DESC query_desc;
    D3D11_TEXTURE2D_DESC desc;
    HRESULT hr;
    int64_t id;
    uint32_t width, height, command_count, command_index;
    int64_t pos = 4;

    if (width_arg <= 0 || height_arg <= 0 || width_arg > UINT_MAX || height_arg > UINT_MAX ||
        !rt_directx_stream_valid((uint32_t)width_arg, (uint32_t)height_arg, words, words_len)) return 0;
    if (!rt_directx_enter()) return 0;
    submission = (RtDirectXSubmission *)calloc(1, sizeof(*submission));
    if (!submission) goto fail;
    if (!rt_directx_open_device(&submission->device)) goto fail;
    width = (uint32_t)width_arg;
    height = (uint32_t)height_arg;
    memset(&desc, 0, sizeof(desc));
    desc.Width = width;
    desc.Height = height;
    desc.MipLevels = 1;
    desc.ArraySize = 1;
    desc.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    desc.SampleDesc.Count = 1;
    desc.Usage = D3D11_USAGE_DEFAULT;
    desc.BindFlags = D3D11_BIND_RENDER_TARGET;
    hr = ID3D11Device_CreateTexture2D(submission->device.device, &desc, NULL, &submission->target);
    if (FAILED(hr) || !submission->target) goto fail;
    hr = ID3D11Device_CreateRenderTargetView(submission->device.device, (ID3D11Resource *)submission->target,
                                               NULL, &submission->view);
    if (FAILED(hr) || !submission->view) goto fail;
    command_count = (uint32_t)words[2];
    for (command_index = 0; command_index < command_count; command_index++) {
        uint32_t op = (uint32_t)words[pos + 0];
        uint32_t record_words = (uint32_t)words[pos + 1];
        uint32_t x = (uint32_t)words[pos + 2];
        uint32_t y = (uint32_t)words[pos + 3];
        uint32_t w = (uint32_t)words[pos + 4];
        uint32_t h = (uint32_t)words[pos + 5];
        uint32_t arg = (uint32_t)words[pos + 6];
        if (op == RT_DX11_OP_CLEAR) {
            float color[4];
            rt_directx_argb_color(arg, color);
            ID3D11DeviceContext_ClearRenderTargetView(submission->device.context, submission->view, color);
        } else if (op == RT_DX11_OP_RECT) {
            float color[4];
            D3D11_RECT rect;
            rect.left = (LONG)x;
            rect.top = (LONG)y;
            rect.right = (LONG)(x + w);
            rect.bottom = (LONG)(y + h);
            rt_directx_argb_color(arg, color);
            ID3D11DeviceContext1_ClearView(submission->device.context1, (ID3D11View *)submission->view, color, &rect, 1);
        } else {
            D3D11_BOX box;
            uint32_t payload_words = (uint32_t)words[pos + 7];
            size_t image_bytes = (size_t)payload_words * sizeof(uint32_t);
            uint32_t *image_pixels;
            uint32_t pixel_index;
            if (payload_words != 0 && image_bytes / sizeof(uint32_t) != payload_words) goto fail;
            image_pixels = (uint32_t *)malloc(image_bytes);
            if (!image_pixels) goto fail;
            for (pixel_index = 0; pixel_index < payload_words; pixel_index++) {
                image_pixels[pixel_index] = (uint32_t)words[pos + RT_DX11_RECORD_WORDS + pixel_index];
            }
            box.left = x;
            box.top = y;
            box.front = 0;
            box.right = x + w;
            box.bottom = y + h;
            box.back = 1;
            ID3D11DeviceContext_UpdateSubresource(submission->device.context, (ID3D11Resource *)submission->target,
                                                  0, &box, image_pixels, w * sizeof(uint32_t), 0);
            free(image_pixels);
        }
        pos += record_words;
    }
    desc.Usage = D3D11_USAGE_STAGING;
    desc.BindFlags = 0;
    desc.CPUAccessFlags = D3D11_CPU_ACCESS_READ;
    hr = ID3D11Device_CreateTexture2D(submission->device.device, &desc, NULL, &submission->staging);
    if (FAILED(hr) || !submission->staging) goto fail;
    ID3D11DeviceContext_CopyResource(submission->device.context, (ID3D11Resource *)submission->staging,
                                     (ID3D11Resource *)submission->target);
    memset(&query_desc, 0, sizeof(query_desc));
    query_desc.Query = D3D11_QUERY_EVENT;
    hr = ID3D11Device_CreateQuery(submission->device.device, &query_desc, &submission->event_query);
    if (FAILED(hr) || !submission->event_query) goto fail;

    /* PR-B fence creation/signalling belongs here, under rt_directx_lock and
     * before the ID is published. It can use rt_directx_submission_find only
     * after publication, so a fence implementation needing submit ordering
     * must operate on this local record and fail closed when Device5/Context4
     * are unavailable. End queues the event after the target draw and staging
     * copy work above. The
     * scheduler must later poll GetData; event creation is not completion. */
    ID3D11DeviceContext_End(submission->device.context, (ID3D11Asynchronous *)submission->event_query);
    ID3D11DeviceContext_Flush(submission->device.context);
    if (rt_directx_next_submission_id <= 0 || rt_directx_next_submission_id == INT64_MAX) goto fail;
    id = rt_directx_next_submission_id++;
    submission->id = id;
    submission->phase = RT_DX11_SUBMISSION_SUBMITTED;
    submission->next = rt_directx_submissions;
    rt_directx_submissions = submission;
    rt_directx_leave();
    return id;

fail:
    if (submission) {
        rt_directx_submission_release(submission);
        free(submission);
    }
    rt_directx_leave();
    return 0;
}

int64_t rt_directx_submission_poll(int64_t submission_id) {
    RtDirectXSubmission *submission;
    int phase;
    if (submission_id <= 0 || !rt_directx_enter()) return -1;
    submission = rt_directx_submission_find(submission_id);
    if (!submission && rt_directx_submission_was_retired(submission_id)) {
        rt_directx_leave();
        return RT_DX11_SUBMISSION_RETIRED;
    }
    phase = rt_directx_submission_poll_locked(submission);
    rt_directx_leave();
    return phase;
}

int64_t rt_directx_submission_complete(int64_t submission_id) {
    RtDirectXSubmission *submission;
    int phase;
    if (submission_id <= 0 || !rt_directx_enter()) return -1;
    submission = rt_directx_submission_find(submission_id);
    phase = rt_directx_submission_poll_locked(submission);
    if (phase == RT_DX11_SUBMISSION_GPU_FINISHED) {
        submission->phase = RT_DX11_SUBMISSION_COMPLETED;
        phase = submission->phase;
    }
    rt_directx_leave();
    return phase;
}

int64_t rt_directx_submission_retire(int64_t submission_id) {
    RtDirectXSubmission *submission;
    int phase;
    if (submission_id <= 0 || !rt_directx_enter()) return -1;
    submission = rt_directx_submission_find(submission_id);
    if (!submission) {
        rt_directx_leave();
        return -1;
    }
    if (submission->phase == RT_DX11_SUBMISSION_COMPLETED) {
        rt_directx_submission_note_retired(submission->id);
        rt_directx_submission_unlink_and_free(submission);
        phase = RT_DX11_SUBMISSION_RETIRED;
        rt_directx_leave();
        return phase;
    }
    phase = submission->phase;
    rt_directx_leave();
    return phase;
}

int64_t rt_directx_submission_abandon(int64_t submission_id) {
    RtDirectXSubmission *submission;
    if (submission_id <= 0 || !rt_directx_enter()) return 0;
    submission = rt_directx_submission_find(submission_id);
    if (!submission) {
        rt_directx_leave();
        return 0;
    }
    rt_directx_submission_unlink_and_free(submission);
    rt_directx_leave();
    return 1;
}

int64_t rt_directx_submission_readback_pixel(int64_t submission_id) {
    RtDirectXSubmission *submission;
    D3D11_MAPPED_SUBRESOURCE mapped;
    HRESULT hr;
    uint32_t pixel;
    if (submission_id <= 0 || !rt_directx_enter()) return -1;
    submission = rt_directx_submission_find(submission_id);
    if (!submission || rt_directx_submission_poll_locked(submission) != RT_DX11_SUBMISSION_GPU_FINISHED ||
        !submission->staging || !submission->device.context) {
        rt_directx_leave();
        return -1;
    }
    memset(&mapped, 0, sizeof(mapped));
    hr = ID3D11DeviceContext_Map(submission->device.context, (ID3D11Resource *)submission->staging,
                                 0, D3D11_MAP_READ, 0, &mapped);
    if (FAILED(hr) || !mapped.pData || mapped.RowPitch < sizeof(uint32_t)) {
        rt_directx_leave();
        return -1;
    }
    memcpy(&pixel, mapped.pData, sizeof(pixel));
    ID3D11DeviceContext_Unmap(submission->device.context, (ID3D11Resource *)submission->staging, 0);
    rt_directx_leave();
    return (int64_t)pixel;
}

int64_t rt_directx_execute_readback_checked(int64_t width_arg, int64_t height_arg,
                                            const int64_t *words, int64_t words_len,
                                            uint32_t *out, int64_t out_len) {
    RtDirectXDevice state;
    ID3D11Texture2D *target = NULL;
    ID3D11RenderTargetView *view = NULL;
    ID3D11Texture2D *staging = NULL;
    D3D11_TEXTURE2D_DESC desc;
    D3D11_MAPPED_SUBRESOURCE mapped;
    uint32_t width, height, command_count;
    uint64_t pixel_count;
    int64_t pos = 4;
    uint32_t command_index;
    int mapped_ok = 0;
    int64_t token = 0;
    HRESULT hr;

    if (width_arg <= 0 || height_arg <= 0 || width_arg > UINT_MAX || height_arg > UINT_MAX || !out) return 0;
    width = (uint32_t)width_arg;
    height = (uint32_t)height_arg;
    pixel_count = (uint64_t)width * (uint64_t)height;
    if (pixel_count > INT64_MAX - 2 || out_len != (int64_t)pixel_count + 2 ||
        !rt_directx_stream_valid(width, height, words, words_len)) return 0;
    if (!rt_directx_enter()) return 0;
    memset(&state, 0, sizeof(state));
    memset(&desc, 0, sizeof(desc));
    memset(&mapped, 0, sizeof(mapped));

    if (!rt_directx_open_device(&state)) goto cleanup;
    desc.Width = width;
    desc.Height = height;
    desc.MipLevels = 1;
    desc.ArraySize = 1;
    desc.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    desc.SampleDesc.Count = 1;
    desc.Usage = D3D11_USAGE_DEFAULT;
    desc.BindFlags = D3D11_BIND_RENDER_TARGET;
    hr = ID3D11Device_CreateTexture2D(state.device, &desc, NULL, &target);
    if (FAILED(hr) || !target) goto cleanup;
    hr = ID3D11Device_CreateRenderTargetView(state.device, (ID3D11Resource *)target, NULL, &view);
    if (FAILED(hr) || !view) goto cleanup;

    command_count = (uint32_t)words[2];
    for (command_index = 0; command_index < command_count; command_index++) {
        uint32_t op = (uint32_t)words[pos + 0];
        uint32_t record_words = (uint32_t)words[pos + 1];
        uint32_t x = (uint32_t)words[pos + 2];
        uint32_t y = (uint32_t)words[pos + 3];
        uint32_t w = (uint32_t)words[pos + 4];
        uint32_t h = (uint32_t)words[pos + 5];
        uint32_t arg = (uint32_t)words[pos + 6];
        if (op == RT_DX11_OP_CLEAR) {
            float color[4];
            rt_directx_argb_color(arg, color);
            ID3D11DeviceContext_ClearRenderTargetView(state.context, view, color);
        } else if (op == RT_DX11_OP_RECT) {
            float color[4];
            D3D11_RECT rect;
            rect.left = (LONG)x;
            rect.top = (LONG)y;
            rect.right = (LONG)(x + w);
            rect.bottom = (LONG)(y + h);
            rt_directx_argb_color(arg, color);
            ID3D11DeviceContext1_ClearView(state.context1, (ID3D11View *)view, color, &rect, 1);
        } else {
            D3D11_BOX box;
            uint32_t payload_words = (uint32_t)words[pos + 7];
            size_t image_bytes = (size_t)payload_words * sizeof(uint32_t);
            if (payload_words != 0 && image_bytes / sizeof(uint32_t) != payload_words) goto cleanup;
            uint32_t *image_pixels = (uint32_t *)malloc(image_bytes);
            uint32_t pixel_index;
            if (!image_pixels) goto cleanup;
            for (pixel_index = 0; pixel_index < payload_words; pixel_index++) {
                image_pixels[pixel_index] = (uint32_t)words[pos + RT_DX11_RECORD_WORDS + pixel_index];
            }
            box.left = x;
            box.top = y;
            box.front = 0;
            box.right = x + w;
            box.bottom = y + h;
            box.back = 1;
            ID3D11DeviceContext_UpdateSubresource(state.context, (ID3D11Resource *)target, 0, &box,
                                                  image_pixels, w * sizeof(uint32_t), 0);
            free(image_pixels);
        }
        pos += record_words;
    }

    desc.Usage = D3D11_USAGE_STAGING;
    desc.BindFlags = 0;
    desc.CPUAccessFlags = D3D11_CPU_ACCESS_READ;
    hr = ID3D11Device_CreateTexture2D(state.device, &desc, NULL, &staging);
    if (FAILED(hr) || !staging) goto cleanup;
    ID3D11DeviceContext_CopyResource(state.context, (ID3D11Resource *)staging, (ID3D11Resource *)target);
    ID3D11DeviceContext_Flush(state.context);
    hr = ID3D11DeviceContext_Map(state.context, (ID3D11Resource *)staging, 0, D3D11_MAP_READ, 0, &mapped);
    if (FAILED(hr) || !mapped.pData || mapped.RowPitch < width * sizeof(uint32_t)) goto cleanup;
    mapped_ok = 1;
    for (uint32_t row = 0; row < height; row++) {
        memcpy(out + 2 + (uint64_t)row * width,
               (const uint8_t *)mapped.pData + (uint64_t)row * mapped.RowPitch,
               (size_t)width * sizeof(uint32_t));
    }
    token = (int64_t)((uintptr_t)target & (uintptr_t)INT64_MAX);
    if (token <= 0) token = 0;
    if (token > 0) {
        uint64_t identity = (uint64_t)state.identity;
        out[0] = (uint32_t)identity;
        out[1] = (uint32_t)(identity >> 32);
    }

cleanup:
    if (mapped_ok) ID3D11DeviceContext_Unmap(state.context, (ID3D11Resource *)staging, 0);
    if (staging) ID3D11Texture2D_Release(staging);
    if (view) ID3D11RenderTargetView_Release(view);
    if (target) ID3D11Texture2D_Release(target);
    rt_directx_close_device(&state);
    rt_directx_leave();
    return token;
}

int64_t rt_directx_hardware_adapter_identity(void) {
    RtDirectXDevice state;
    int64_t identity = 0;
    if (!rt_directx_enter()) return 0;
    if (rt_directx_open_device(&state)) {
        identity = state.identity;
        rt_directx_close_device(&state);
    }
    rt_directx_leave();
    return identity;
}

#else

int64_t rt_directx_execute_readback_checked(int64_t width, int64_t height,
                                            const int64_t *words, int64_t words_len,
                                            uint32_t *out, int64_t out_len) {
    (void)width;
    (void)height;
    (void)words;
    (void)words_len;
    (void)out;
    (void)out_len;
    return 0;
}

int64_t rt_directx_hardware_adapter_identity(void) {
    return 0;
}

int64_t rt_directx_submission_submit(int64_t width, int64_t height,
                                     const int64_t *words, int64_t words_len) {
    (void)width;
    (void)height;
    (void)words;
    (void)words_len;
    return 0;
}

int64_t rt_directx_submission_poll(int64_t submission_id) {
    (void)submission_id;
    return -1;
}

int64_t rt_directx_submission_complete(int64_t submission_id) {
    (void)submission_id;
    return -1;
}

int64_t rt_directx_submission_retire(int64_t submission_id) {
    (void)submission_id;
    return -1;
}

int64_t rt_directx_submission_abandon(int64_t submission_id) {
    (void)submission_id;
    return 0;
}

int64_t rt_directx_submission_readback_pixel(int64_t submission_id) {
    (void)submission_id;
    return -1;
}

#endif
