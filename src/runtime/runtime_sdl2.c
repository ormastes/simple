/*
 * Simple SDL2 Windowing Runtime
 *
 * Thin SDL2 C wrapper providing rt_sdl2_* functions for the Simple 2D
 * game engine. Replaces the Rust winit-based windowing system with a
 * pure C implementation using SDL2's software rendering path.
 *
 * Pixel format: each pixel is an i64 packed as R*16777216 + G*65536 + B*256 + A
 * (RGBA, high byte to low byte). The pixel buffer is a SplArray* of i64 values.
 *
 * SDL2 is loaded DYNAMICALLY at first use (dlopen/dlsym, LoadLibrary/GetProcAddress)
 * exactly as SDL itself does it. No SDL2 headers are needed to build this file and
 * no -lSDL2 is needed to link it, so a host without SDL2 still builds and links; a
 * missing library degrades to an honest runtime refusal (rt_sdl2_init() -> 0,
 * rt_sdl2_last_error() -> the soname list that was tried) instead of a link error.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_sdl2.c -o runtime_sdl2.o
 * Link:  (nothing; libdl only where it is a separate library)
 */

#include "runtime.h"

#include <limits.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ================================================================
 * SDL2 ABI (header-free)
 *
 * Every offset, size and constant below was generated from the real
 * SDL2 headers (2.30.0) with an offsetof/sizeof probe -- see the
 * static asserts at the end of this block, which re-verify the layout
 * at compile time on every build.
 * ================================================================ */

typedef uint8_t  Uint8;
typedef uint16_t Uint16;
typedef uint32_t Uint32;
typedef uint64_t Uint64;
typedef int32_t  Sint32;
typedef int      SDL_bool;

#define SDL_FALSE 0
#define SDL_TRUE  1

typedef struct SDL_Window SDL_Window;
typedef uint32_t SDL_AudioDeviceID;

typedef struct { int x, y, w, h; } SDL_Rect;

typedef struct {
    Uint32 flags;          /* 0 */
    void*  format;         /* 8 */
    int    w, h;           /* 16, 20 */
    int    pitch;          /* 24 */
    void*  pixels;         /* 32 */
    /* remainder of SDL_Surface (userdata, locked, list_blitmap, clip_rect,
       map, refcount) is never touched here; pad to the real 96 bytes so a
       stack/array of SDL_Surface would still be correctly sized. */
    char   _tail[96 - 40];
} SDL_Surface;

typedef struct {
    int    scancode;       /* 0 */
    int    sym;            /* 4 */
    Uint16 mod;            /* 8 */
    Uint32 unused;         /* 12 */
} SDL_Keysym;

typedef union {
    Uint32 type;
    struct { Uint32 type, timestamp; Uint32 windowID; Uint8 state, repeat, pad2, pad3;
             SDL_Keysym keysym; } key;
    struct { Uint32 type, timestamp; Uint32 windowID; char text[32]; } text;
    struct { Uint32 type, timestamp; Uint32 windowID, which, state; Sint32 x, y, xrel, yrel; } motion;
    struct { Uint32 type, timestamp; Uint32 windowID, which; Uint8 button, state, clicks, padding1;
             Sint32 x, y; } button;
    struct { Uint32 type, timestamp; Uint32 windowID, which; Sint32 x, y; Uint32 direction; } wheel;
    struct { Uint32 type, timestamp; Uint32 windowID; Uint8 event, padding1, padding2, padding3;
             Sint32 data1, data2; } window;
    Uint8 padding[56];
} SDL_Event;

typedef void (*SDL_AudioCallback)(void* userdata, Uint8* stream, int len);

typedef struct {
    int    freq;              /* 0 */
    Uint16 format;            /* 4 */
    Uint8  channels;          /* 6 */
    Uint8  silence;           /* 7 */
    Uint16 samples;           /* 8 */
    Uint16 padding;           /* 10 */
    Uint32 size;              /* 12 */
    SDL_AudioCallback callback; /* 16 */
    void*  userdata;          /* 24 */
} SDL_AudioSpec;

#define SDL_INIT_AUDIO   0x00000010u
#define SDL_INIT_VIDEO   0x00000020u
#define SDL_INIT_EVENTS  0x00004000u

#define SDL_QUIT             0x100u
#define SDL_WINDOWEVENT      0x200u
#define SDL_KEYDOWN          0x300u
#define SDL_KEYUP            0x301u
#define SDL_TEXTINPUT        0x303u
#define SDL_MOUSEMOTION      0x400u
#define SDL_MOUSEBUTTONDOWN  0x401u
#define SDL_MOUSEBUTTONUP    0x402u
#define SDL_MOUSEWHEEL       0x403u

#define SDL_WINDOW_SHOWN               0x00000004u
#define SDL_WINDOW_RESIZABLE           0x00000020u
#define SDL_WINDOW_INPUT_FOCUS         0x00000200u
#define SDL_WINDOW_FULLSCREEN_DESKTOP  0x00001001u
#define SDL_WINDOWPOS_CENTERED         0x2FFF0000u

#define SDL_BUTTON_LEFT    1
#define SDL_BUTTON_MIDDLE  2
#define SDL_BUTTON_RIGHT   3
#define SDL_BUTTON_LMASK   0x1u
#define SDL_BUTTON_MMASK   0x2u
#define SDL_BUTTON_RMASK   0x4u

#define SDL_DISABLE 0
#define SDL_ENABLE  1

#define AUDIO_F32LSB 0x8120u
#define AUDIO_F32MSB 0x9120u
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define AUDIO_F32SYS AUDIO_F32MSB
#else
#define AUDIO_F32SYS AUDIO_F32LSB
#endif

#define SDL_zero(x) memset(&(x), 0, sizeof((x)))

/* Compile-time re-verification of the probed layout. */
#define RT_SDL2_ASSERT(cond, tag) typedef char rt_sdl2_static_##tag[(cond) ? 1 : -1]
RT_SDL2_ASSERT(sizeof(SDL_Event) == 56, event_size);
RT_SDL2_ASSERT(sizeof(SDL_Surface) == 96, surface_size);
RT_SDL2_ASSERT(sizeof(SDL_AudioSpec) == 32, audiospec_size);
RT_SDL2_ASSERT(sizeof(SDL_Rect) == 16, rect_size);
RT_SDL2_ASSERT(sizeof(SDL_Keysym) == 16, keysym_size);
RT_SDL2_ASSERT(offsetof(SDL_Event, key.keysym) == 16, key_keysym);
RT_SDL2_ASSERT(offsetof(SDL_Event, text.text) == 12, text_text);
RT_SDL2_ASSERT(offsetof(SDL_Event, motion.x) == 20, motion_x);
RT_SDL2_ASSERT(offsetof(SDL_Event, button.button) == 16, button_button);
RT_SDL2_ASSERT(offsetof(SDL_Event, button.x) == 20, button_x);
RT_SDL2_ASSERT(offsetof(SDL_Event, wheel.x) == 16, wheel_x);
RT_SDL2_ASSERT(offsetof(SDL_Event, window.event) == 12, window_event);
RT_SDL2_ASSERT(offsetof(SDL_Event, window.data1) == 16, window_data1);
RT_SDL2_ASSERT(offsetof(SDL_Surface, w) == 16, surface_w);
RT_SDL2_ASSERT(offsetof(SDL_Surface, pitch) == 24, surface_pitch);
RT_SDL2_ASSERT(offsetof(SDL_Surface, pixels) == 32, surface_pixels);
RT_SDL2_ASSERT(offsetof(SDL_AudioSpec, callback) == 16, audiospec_callback);

/* ================================================================
 * Dynamic loader
 * ================================================================ */

#if defined(_WIN32)
#include <windows.h>
static void* sdl2_open(const char* name) { return (void*)LoadLibraryA(name); }
static void* sdl2_symbol(void* lib, const char* name) {
    return lib ? (void*)(uintptr_t)GetProcAddress((HMODULE)lib, name) : NULL;
}
#else
#include <dlfcn.h>
static void* sdl2_open(const char* name) { return dlopen(name, RTLD_NOW | RTLD_LOCAL); }
static void* sdl2_symbol(void* lib, const char* name) { return lib ? dlsym(lib, name) : NULL; }
#endif

/*
 * Candidate sonames, most-specific first -- the same order SDL's own loader
 * uses. The versioned soname is tried before the unversioned developer
 * symlink, because the latter is only present when a -dev package is
 * installed and is not what a deployed application should bind to.
 */
static const char* const g_sdl2_candidates[] = {
#if defined(_WIN32)
    "SDL2.dll",
#elif defined(__APPLE__)
    "libSDL2-2.0.0.dylib", "libSDL2-2.0.dylib", "libSDL2.dylib",
#else
    "libSDL2-2.0.so.0", "libSDL2-2.0.so", "libSDL2.so.0", "libSDL2.so",
#endif
    NULL
};

static void*       g_sdl2_library;
static const char* g_sdl2_resolved;          /* soname that actually opened */
static int         g_sdl2_load_attempted;
static char        g_sdl2_load_error[512];

/* Every SDL2 entry point this file uses, resolved at first use. */
static int         (*p_SDL_Init)(Uint32);
static void        (*p_SDL_Quit)(void);
static int         (*p_SDL_InitSubSystem)(Uint32);
static void        (*p_SDL_QuitSubSystem)(Uint32);
static Uint32      (*p_SDL_WasInit)(Uint32);
static const char* (*p_SDL_GetError)(void);
static void        (*p_SDL_free)(void*);
static SDL_Window* (*p_SDL_CreateWindow)(const char*, int, int, int, int, Uint32);
static void        (*p_SDL_DestroyWindow)(SDL_Window*);
static void        (*p_SDL_GetWindowSize)(SDL_Window*, int*, int*);
static void        (*p_SDL_SetWindowTitle)(SDL_Window*, const char*);
static SDL_Surface*(*p_SDL_GetWindowSurface)(SDL_Window*);
static int         (*p_SDL_UpdateWindowSurface)(SDL_Window*);
static SDL_Surface*(*p_SDL_CreateRGBSurfaceFrom)(void*, int, int, int, int,
                                                 Uint32, Uint32, Uint32, Uint32);
static void        (*p_SDL_FreeSurface)(SDL_Surface*);
static int         (*p_SDL_UpperBlitScaled)(SDL_Surface*, const SDL_Rect*, SDL_Surface*, SDL_Rect*);
static int         (*p_SDL_PollEvent)(SDL_Event*);
static int         (*p_SDL_WaitEvent)(SDL_Event*);
static int         (*p_SDL_WaitEventTimeout)(SDL_Event*, int);
static const Uint8*(*p_SDL_GetKeyboardState)(int*);
static Uint32      (*p_SDL_GetMouseState)(int*, int*);
static Uint32      (*p_SDL_GetTicks)(void);
static Uint64      (*p_SDL_GetPerformanceCounter)(void);
static Uint64      (*p_SDL_GetPerformanceFrequency)(void);
static void        (*p_SDL_StartTextInput)(void);
static void        (*p_SDL_StopTextInput)(void);
static int         (*p_SDL_ShowCursor)(int);
static void        (*p_SDL_SetWindowGrab)(SDL_Window*, SDL_bool);
static void        (*p_SDL_WarpMouseInWindow)(SDL_Window*, int, int);
static char*       (*p_SDL_GetClipboardText)(void);
static int         (*p_SDL_SetClipboardText)(const char*);
static SDL_bool    (*p_SDL_HasClipboardText)(void);
static int         (*p_SDL_GetNumVideoDisplays)(void);
static const char* (*p_SDL_GetDisplayName)(int);
static int         (*p_SDL_GetDisplayBounds)(int, SDL_Rect*);
static int         (*p_SDL_GetDisplayUsableBounds)(int, SDL_Rect*);
static int         (*p_SDL_GetDisplayDPI)(int, float*, float*, float*);
static void        (*p_SDL_SetWindowResizable)(SDL_Window*, SDL_bool);
static int         (*p_SDL_SetWindowFullscreen)(SDL_Window*, Uint32);
static void        (*p_SDL_SetWindowSize)(SDL_Window*, int, int);
static void        (*p_SDL_SetWindowPosition)(SDL_Window*, int, int);
static void        (*p_SDL_GetWindowPosition)(SDL_Window*, int*, int*);
static void        (*p_SDL_ShowWindow)(SDL_Window*);
static void        (*p_SDL_HideWindow)(SDL_Window*);
static void        (*p_SDL_SetWindowMinimumSize)(SDL_Window*, int, int);
static void        (*p_SDL_SetWindowMaximumSize)(SDL_Window*, int, int);
static void        (*p_SDL_MinimizeWindow)(SDL_Window*);
static void        (*p_SDL_MaximizeWindow)(SDL_Window*);
static void        (*p_SDL_RestoreWindow)(SDL_Window*);
static void        (*p_SDL_RaiseWindow)(SDL_Window*);
static void        (*p_SDL_SetWindowBordered)(SDL_Window*, SDL_bool);
static Uint32      (*p_SDL_GetWindowFlags)(SDL_Window*);
static SDL_AudioDeviceID (*p_SDL_OpenAudioDevice)(const char*, int, const SDL_AudioSpec*,
                                                  SDL_AudioSpec*, int);
static void        (*p_SDL_CloseAudioDevice)(SDL_AudioDeviceID);
static void        (*p_SDL_PauseAudioDevice)(SDL_AudioDeviceID, int);
static int         (*p_SDL_QueueAudio)(SDL_AudioDeviceID, const void*, Uint32);
static Uint32      (*p_SDL_GetQueuedAudioSize)(SDL_AudioDeviceID);
static void        (*p_SDL_ClearQueuedAudio)(SDL_AudioDeviceID);
/* Optional: added in SDL 2.0.16. Absence is not a load failure. */
static void        (*p_SDL_SetWindowAlwaysOnTop)(SDL_Window*, SDL_bool);

#define SDL2_BIND_REQUIRED(name) do { \
    *(void**)(&p_##name) = sdl2_symbol(g_sdl2_library, #name); \
    if (!p_##name) { missing = #name; goto bind_failed; } \
} while (0)

#define SDL2_BIND_OPTIONAL(name) \
    (*(void**)(&p_##name) = sdl2_symbol(g_sdl2_library, #name))

/*
 * Lazy, idempotent. Returns 1 when SDL2 is usable, 0 when it is not; on
 * failure g_sdl2_load_error carries a human-readable reason naming every
 * soname that was tried, which rt_sdl2_last_error() surfaces to callers.
 */
static int sdl2_load(void) {
    const char* missing;
    if (g_sdl2_library) return 1;
    if (g_sdl2_load_attempted) return 0;
    g_sdl2_load_attempted = 1;

    for (int i = 0; g_sdl2_candidates[i] && !g_sdl2_library; ++i) {
        g_sdl2_library = sdl2_open(g_sdl2_candidates[i]);
        if (g_sdl2_library) g_sdl2_resolved = g_sdl2_candidates[i];
    }
    if (!g_sdl2_library) {
        size_t used = (size_t)snprintf(g_sdl2_load_error, sizeof(g_sdl2_load_error),
                                       "SDL2 unavailable: none of these could be loaded:");
        for (int i = 0; g_sdl2_candidates[i] && used < sizeof(g_sdl2_load_error); ++i) {
            used += (size_t)snprintf(g_sdl2_load_error + used, sizeof(g_sdl2_load_error) - used,
                                     "%s %s", i ? "," : "", g_sdl2_candidates[i]);
        }
        return 0;
    }

    SDL2_BIND_REQUIRED(SDL_Init);
    SDL2_BIND_REQUIRED(SDL_Quit);
    SDL2_BIND_REQUIRED(SDL_InitSubSystem);
    SDL2_BIND_REQUIRED(SDL_QuitSubSystem);
    SDL2_BIND_REQUIRED(SDL_WasInit);
    SDL2_BIND_REQUIRED(SDL_GetError);
    SDL2_BIND_REQUIRED(SDL_free);
    SDL2_BIND_REQUIRED(SDL_CreateWindow);
    SDL2_BIND_REQUIRED(SDL_DestroyWindow);
    SDL2_BIND_REQUIRED(SDL_GetWindowSize);
    SDL2_BIND_REQUIRED(SDL_SetWindowTitle);
    SDL2_BIND_REQUIRED(SDL_GetWindowSurface);
    SDL2_BIND_REQUIRED(SDL_UpdateWindowSurface);
    SDL2_BIND_REQUIRED(SDL_CreateRGBSurfaceFrom);
    SDL2_BIND_REQUIRED(SDL_FreeSurface);
    /* SDL_BlitScaled is a macro in SDL_surface.h; the exported symbol is
       SDL_UpperBlitScaled. Binding "SDL_BlitScaled" would silently yield NULL. */
    SDL2_BIND_REQUIRED(SDL_UpperBlitScaled);
    SDL2_BIND_REQUIRED(SDL_PollEvent);
    SDL2_BIND_REQUIRED(SDL_WaitEvent);
    SDL2_BIND_REQUIRED(SDL_WaitEventTimeout);
    SDL2_BIND_REQUIRED(SDL_GetKeyboardState);
    SDL2_BIND_REQUIRED(SDL_GetMouseState);
    SDL2_BIND_REQUIRED(SDL_GetTicks);
    SDL2_BIND_REQUIRED(SDL_GetPerformanceCounter);
    SDL2_BIND_REQUIRED(SDL_GetPerformanceFrequency);
    SDL2_BIND_REQUIRED(SDL_StartTextInput);
    SDL2_BIND_REQUIRED(SDL_StopTextInput);
    SDL2_BIND_REQUIRED(SDL_ShowCursor);
    SDL2_BIND_REQUIRED(SDL_SetWindowGrab);
    SDL2_BIND_REQUIRED(SDL_WarpMouseInWindow);
    SDL2_BIND_REQUIRED(SDL_GetClipboardText);
    SDL2_BIND_REQUIRED(SDL_SetClipboardText);
    SDL2_BIND_REQUIRED(SDL_HasClipboardText);
    SDL2_BIND_REQUIRED(SDL_GetNumVideoDisplays);
    SDL2_BIND_REQUIRED(SDL_GetDisplayName);
    SDL2_BIND_REQUIRED(SDL_GetDisplayBounds);
    SDL2_BIND_REQUIRED(SDL_GetDisplayUsableBounds);
    SDL2_BIND_REQUIRED(SDL_GetDisplayDPI);
    SDL2_BIND_REQUIRED(SDL_SetWindowResizable);
    SDL2_BIND_REQUIRED(SDL_SetWindowFullscreen);
    SDL2_BIND_REQUIRED(SDL_SetWindowSize);
    SDL2_BIND_REQUIRED(SDL_SetWindowPosition);
    SDL2_BIND_REQUIRED(SDL_GetWindowPosition);
    SDL2_BIND_REQUIRED(SDL_ShowWindow);
    SDL2_BIND_REQUIRED(SDL_HideWindow);
    SDL2_BIND_REQUIRED(SDL_SetWindowMinimumSize);
    SDL2_BIND_REQUIRED(SDL_SetWindowMaximumSize);
    SDL2_BIND_REQUIRED(SDL_MinimizeWindow);
    SDL2_BIND_REQUIRED(SDL_MaximizeWindow);
    SDL2_BIND_REQUIRED(SDL_RestoreWindow);
    SDL2_BIND_REQUIRED(SDL_RaiseWindow);
    SDL2_BIND_REQUIRED(SDL_SetWindowBordered);
    SDL2_BIND_REQUIRED(SDL_GetWindowFlags);
    SDL2_BIND_REQUIRED(SDL_OpenAudioDevice);
    SDL2_BIND_REQUIRED(SDL_CloseAudioDevice);
    SDL2_BIND_REQUIRED(SDL_PauseAudioDevice);
    SDL2_BIND_REQUIRED(SDL_QueueAudio);
    SDL2_BIND_REQUIRED(SDL_GetQueuedAudioSize);
    SDL2_BIND_REQUIRED(SDL_ClearQueuedAudio);
    SDL2_BIND_OPTIONAL(SDL_SetWindowAlwaysOnTop);
    return 1;

bind_failed:
    snprintf(g_sdl2_load_error, sizeof(g_sdl2_load_error),
             "SDL2 unusable: %s loaded but symbol %s is missing",
             g_sdl2_resolved ? g_sdl2_resolved : "(library)", missing);
    g_sdl2_library = NULL;
    g_sdl2_resolved = NULL;
    return 0;
}

/*
 * Route every SDL2 call in the body of this file through the resolved
 * pointer. The bodies below are unchanged from the link-time version.
 */
#define SDL_Init                    p_SDL_Init
#define SDL_Quit                    p_SDL_Quit
#define SDL_InitSubSystem           p_SDL_InitSubSystem
#define SDL_QuitSubSystem           p_SDL_QuitSubSystem
#define SDL_WasInit                 p_SDL_WasInit
#define SDL_GetError                p_SDL_GetError
#define SDL_free                    p_SDL_free
#define SDL_CreateWindow            p_SDL_CreateWindow
#define SDL_DestroyWindow           p_SDL_DestroyWindow
#define SDL_GetWindowSize           p_SDL_GetWindowSize
#define SDL_SetWindowTitle          p_SDL_SetWindowTitle
#define SDL_GetWindowSurface        p_SDL_GetWindowSurface
#define SDL_UpdateWindowSurface     p_SDL_UpdateWindowSurface
#define SDL_CreateRGBSurfaceFrom    p_SDL_CreateRGBSurfaceFrom
#define SDL_FreeSurface             p_SDL_FreeSurface
#define SDL_BlitScaled              p_SDL_UpperBlitScaled
#define SDL_PollEvent               p_SDL_PollEvent
#define SDL_WaitEvent               p_SDL_WaitEvent
#define SDL_WaitEventTimeout        p_SDL_WaitEventTimeout
#define SDL_GetKeyboardState        p_SDL_GetKeyboardState
#define SDL_GetMouseState           p_SDL_GetMouseState
#define SDL_GetTicks                p_SDL_GetTicks
#define SDL_GetPerformanceCounter   p_SDL_GetPerformanceCounter
#define SDL_GetPerformanceFrequency p_SDL_GetPerformanceFrequency
#define SDL_StartTextInput          p_SDL_StartTextInput
#define SDL_StopTextInput           p_SDL_StopTextInput
#define SDL_ShowCursor              p_SDL_ShowCursor
#define SDL_SetWindowGrab           p_SDL_SetWindowGrab
#define SDL_WarpMouseInWindow       p_SDL_WarpMouseInWindow
#define SDL_GetClipboardText        p_SDL_GetClipboardText
#define SDL_SetClipboardText        p_SDL_SetClipboardText
#define SDL_HasClipboardText        p_SDL_HasClipboardText
#define SDL_GetNumVideoDisplays     p_SDL_GetNumVideoDisplays
#define SDL_GetDisplayName          p_SDL_GetDisplayName
#define SDL_GetDisplayBounds        p_SDL_GetDisplayBounds
#define SDL_GetDisplayUsableBounds  p_SDL_GetDisplayUsableBounds
#define SDL_GetDisplayDPI           p_SDL_GetDisplayDPI
#define SDL_SetWindowResizable      p_SDL_SetWindowResizable
#define SDL_SetWindowFullscreen     p_SDL_SetWindowFullscreen
#define SDL_SetWindowSize           p_SDL_SetWindowSize
#define SDL_SetWindowPosition       p_SDL_SetWindowPosition
#define SDL_GetWindowPosition       p_SDL_GetWindowPosition
#define SDL_ShowWindow              p_SDL_ShowWindow
#define SDL_HideWindow              p_SDL_HideWindow
#define SDL_SetWindowMinimumSize    p_SDL_SetWindowMinimumSize
#define SDL_SetWindowMaximumSize    p_SDL_SetWindowMaximumSize
#define SDL_MinimizeWindow          p_SDL_MinimizeWindow
#define SDL_MaximizeWindow          p_SDL_MaximizeWindow
#define SDL_RestoreWindow           p_SDL_RestoreWindow
#define SDL_RaiseWindow             p_SDL_RaiseWindow
#define SDL_SetWindowBordered       p_SDL_SetWindowBordered
#define SDL_GetWindowFlags          p_SDL_GetWindowFlags
#define SDL_OpenAudioDevice         p_SDL_OpenAudioDevice
#define SDL_CloseAudioDevice        p_SDL_CloseAudioDevice
#define SDL_PauseAudioDevice        p_SDL_PauseAudioDevice
#define SDL_QueueAudio              p_SDL_QueueAudio
#define SDL_GetQueuedAudioSize      p_SDL_GetQueuedAudioSize
#define SDL_ClearQueuedAudio        p_SDL_ClearQueuedAudio

/*
 * Entry-point gate. SDL2 is loaded on first use; if it is not there, the
 * caller gets this value back rather than a NULL function pointer call.
 */
#define SDL2_REQUIRE(fail_value) do { if (!sdl2_load()) return fail_value; } while (0)
#define SDL2_REQUIRE_VOID()      do { if (!sdl2_load()) return; } while (0)

/* ================================================================
 * Global State
 * ================================================================ */

/* Last polled event — SDL is single-threaded for events */
static SDL_Event g_last_event;
static int       g_last_event_valid = 0;

/* Quit flag — set when SDL_QUIT is received */
static int       g_quit_requested = 0;

/* Performance counter frequency for nanosecond conversion */
static uint64_t  g_perf_freq = 0;

/* One main-thread SDL2 queue device is enough for the current SoundEngine slice. */
static SDL_AudioDeviceID g_audio_device = 0;
static uint32_t g_audio_generation = 0;
static int64_t g_audio_handle = 0;
static int64_t g_audio_submitted_frames = 0;
static int g_audio_owns_subsystem = 0;

/* Generation-checked SDL_Window resources. All table access is confined to
 * the thread that successfully initialized the video/event subsystem. */
#define SDL2_MAX_WINDOWS 64u
#define SDL2_WINDOW_INDEX_MASK (SDL2_MAX_WINDOWS - 1u)
#define SDL2_WINDOW_MAX_GENERATION ((uint64_t)(INT64_MAX - SDL2_MAX_WINDOWS) / SDL2_MAX_WINDOWS)

typedef struct {
    SDL_Window *window;
    uint64_t generation;
} Sdl2WindowSlot;

static Sdl2WindowSlot g_sdl2_windows[SDL2_MAX_WINDOWS];
static uint64_t g_sdl2_next_window_generation = 1;
#if defined(_MSC_VER)
__declspec(thread) static int g_sdl2_thread_token;
#else
static _Thread_local int g_sdl2_thread_token;
#endif
static _Atomic uintptr_t g_sdl2_owner_thread;

static uintptr_t sdl2_current_thread(void) {
    return (uintptr_t)&g_sdl2_thread_token;
}

static bool sdl2_on_owner_thread(void) {
    return atomic_load_explicit(&g_sdl2_owner_thread, memory_order_acquire) ==
           sdl2_current_thread();
}

static int64_t sdl2_window_register(SDL_Window *window) {
    if (!window || !sdl2_on_owner_thread()) return 0;
    for (uint64_t index = 0; index < SDL2_MAX_WINDOWS; index++) {
        Sdl2WindowSlot *slot = &g_sdl2_windows[index];
        if (slot->window) continue;
        uint64_t generation = g_sdl2_next_window_generation++;
        if (generation == 0 || generation > SDL2_WINDOW_MAX_GENERATION) {
            generation = 1;
            g_sdl2_next_window_generation = 2;
        }
        slot->window = window;
        slot->generation = generation;
        return (int64_t)(generation * SDL2_MAX_WINDOWS + index + 1);
    }
    return 0;
}

static Sdl2WindowSlot *sdl2_window_slot(int64_t handle) {
    if (handle <= 0 || !sdl2_on_owner_thread()) return NULL;
    uint64_t encoded = (uint64_t)handle - 1;
    uint64_t index = encoded & SDL2_WINDOW_INDEX_MASK;
    uint64_t generation = encoded / SDL2_MAX_WINDOWS;
    Sdl2WindowSlot *slot = &g_sdl2_windows[index];
    if (generation == 0 || slot->generation != generation || !slot->window)
        return NULL;
    return slot;
}

static SDL_Window *sdl2_window_get(int64_t handle) {
    Sdl2WindowSlot *slot = sdl2_window_slot(handle);
    return slot ? slot->window : NULL;
}

static SDL_Window *sdl2_window_remove(int64_t handle) {
    Sdl2WindowSlot *slot = sdl2_window_slot(handle);
    if (!slot) return NULL;
    SDL_Window *window = slot->window;
    slot->window = NULL;
    return window;
}

/* ================================================================
 * Initialization
 * ================================================================ */

int64_t rt_sdl2_init(void) {
    SDL2_REQUIRE(0);
    uintptr_t thread = sdl2_current_thread();
    uintptr_t owner = atomic_load_explicit(&g_sdl2_owner_thread, memory_order_acquire);
    if (owner != 0 && owner != thread) return 0;
    if (owner == 0 && !atomic_compare_exchange_strong_explicit(
            &g_sdl2_owner_thread, &owner, thread,
            memory_order_acq_rel, memory_order_acquire))
        return 0;
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS) != 0) {
        atomic_store_explicit(&g_sdl2_owner_thread, 0, memory_order_release);
        fprintf(stderr, "[rt_sdl2] SDL_Init failed: %s\n", SDL_GetError());
        return 0;
    }
    g_perf_freq = SDL_GetPerformanceFrequency();
    g_quit_requested = 0;
    g_last_event_valid = 0;
    SDL_StartTextInput();
    return 1;
}

void rt_sdl2_quit(void) {
    SDL2_REQUIRE_VOID();
    if (!sdl2_on_owner_thread()) return;
    for (uint64_t index = 0; index < SDL2_MAX_WINDOWS; index++) {
        SDL_Window *window = g_sdl2_windows[index].window;
        if (window) {
            g_sdl2_windows[index].window = NULL;
            SDL_DestroyWindow(window);
        }
    }
    if (g_audio_handle != 0) {
        rt_audio_sdl2_close(g_audio_handle);
    }
    SDL_StopTextInput();
    SDL_Quit();
    g_quit_requested = 0;
    g_last_event_valid = 0;
    atomic_store_explicit(&g_sdl2_owner_thread, 0, memory_order_release);
}

/* ================================================================
 * SDL2 queued audio
 * ================================================================ */

int64_t rt_audio_sdl2_init(void) {
    SDL2_REQUIRE(0);
    SDL_AudioSpec desired;
    SDL_AudioSpec obtained;

    if (g_audio_handle != 0) return g_audio_handle;

    g_audio_owns_subsystem = SDL_WasInit(SDL_INIT_AUDIO) == 0;
    if (g_audio_owns_subsystem && SDL_InitSubSystem(SDL_INIT_AUDIO) != 0) {
        g_audio_owns_subsystem = 0;
        return 0;
    }

    SDL_zero(desired);
    desired.freq = 48000;
    desired.format = AUDIO_F32SYS;
    desired.channels = 2;
    desired.samples = 1024;
    desired.callback = NULL;
    g_audio_device = SDL_OpenAudioDevice(
        NULL, 0, &desired, &obtained, 0
    );
    if (g_audio_device == 0) {
        if (g_audio_owns_subsystem) SDL_QuitSubSystem(SDL_INIT_AUDIO);
        g_audio_owns_subsystem = 0;
        return 0;
    }

    g_audio_generation++;
    if (g_audio_generation == 0 || g_audio_generation > 0x7fffffffu) {
        g_audio_generation = 1;
    }
    g_audio_handle = (int64_t)(((uint64_t)g_audio_generation << 32) | 1u);
    g_audio_submitted_frames = 0;
    SDL_PauseAudioDevice(g_audio_device, 0);
    return g_audio_handle;
}

int64_t rt_audio_sdl2_queue_pcm_f64_raw(
    int64_t handle,
    int64_t samples_addr,
    int64_t sample_count,
    int64_t channels,
    int64_t sample_rate
) {
    const double* input;
    float* output;
    int64_t frames;
    size_t byte_count;

    if (handle == 0 || handle != g_audio_handle || g_audio_device == 0) return 0;
    if (samples_addr <= 0 || sample_count <= 0) return 0;
    if (channels != 2 || sample_rate != 48000 || sample_count % channels != 0) return 0;
    if ((uint64_t)sample_count > SIZE_MAX / sizeof(float)) return 0;
    if ((uint64_t)sample_count > UINT32_MAX / sizeof(float)) return 0;
    frames = sample_count / channels;
    if (frames > INT64_MAX - g_audio_submitted_frames) return 0;

    byte_count = (size_t)sample_count * sizeof(float);
    output = (float*)malloc(byte_count);
    if (!output) return 0;
    input = (const double*)(uintptr_t)samples_addr;
    for (int64_t i = 0; i < sample_count; i++) {
        double sample = input[i];
        if (sample > 1.0) sample = 1.0;
        if (sample < -1.0) sample = -1.0;
        output[i] = (float)sample;
    }
    if (SDL_QueueAudio(g_audio_device, output, (uint32_t)byte_count) != 0) {
        free(output);
        return 0;
    }
    free(output);

    g_audio_submitted_frames += frames;
    return frames;
}

int64_t rt_audio_sdl2_submitted_frames(int64_t handle) {
    return handle != 0 && handle == g_audio_handle
        ? g_audio_submitted_frames : 0;
}

int64_t rt_audio_sdl2_queued_bytes(int64_t handle) {
    if (handle == 0 || handle != g_audio_handle || g_audio_device == 0) return 0;
    return (int64_t)SDL_GetQueuedAudioSize(g_audio_device);
}

int64_t rt_audio_sdl2_underrun_count(int64_t handle) {
    if (handle == 0 || handle != g_audio_handle) return 0;
    /* SDL2's queue API does not expose hardware underrun accounting. */
    return -1;
}

int64_t rt_audio_sdl2_live_device_count(void) {
    return g_audio_handle != 0 && g_audio_device != 0 ? 1 : 0;
}

int64_t rt_audio_sdl2_close(int64_t handle) {
    if (handle == 0 || handle != g_audio_handle || g_audio_device == 0) return 0;

    SDL_ClearQueuedAudio(g_audio_device);
    SDL_CloseAudioDevice(g_audio_device);
    g_audio_device = 0;
    g_audio_handle = 0;
    g_audio_submitted_frames = 0;
    if (g_audio_owns_subsystem) SDL_QuitSubSystem(SDL_INIT_AUDIO);
    g_audio_owns_subsystem = 0;
    return 1;
}

/* ================================================================
 * Window Management
 * ================================================================ */

int64_t rt_sdl2_create_window(const char* title, int64_t width, int64_t height) {
    SDL2_REQUIRE(0);
    if (!sdl2_on_owner_thread() || width <= 0 || height <= 0 ||
        width > INT_MAX || height > INT_MAX) return 0;
    if (!title) title = "Simple Window";
    SDL_Window* win = SDL_CreateWindow(
        title,
        SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
        (int)width, (int)height,
        SDL_WINDOW_SHOWN | SDL_WINDOW_RESIZABLE
    );
    if (!win) {
        fprintf(stderr, "[rt_sdl2] SDL_CreateWindow failed: %s\n", SDL_GetError());
        return 0;
    }
    int64_t handle = sdl2_window_register(win);
    if (handle == 0) SDL_DestroyWindow(win);
    return handle;
}

void rt_sdl2_destroy_window(int64_t handle) {
    SDL_Window* win = sdl2_window_remove(handle);
    if (!win) return;
    SDL_DestroyWindow(win);
}

int64_t rt_sdl2_get_window_width(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    int w = 0, h = 0;
    SDL_GetWindowSize(win, &w, &h);
    return (int64_t)w;
}

int64_t rt_sdl2_get_window_height(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    int w = 0, h = 0;
    SDL_GetWindowSize(win, &w, &h);
    return (int64_t)h;
}

void rt_sdl2_set_window_title(int64_t handle, const char* title) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win || !title) return;
    SDL_SetWindowTitle(win, title);
}

/* ================================================================
 * Framebuffer Present
 * ================================================================
 *
 * Receives a SplArray* of i64 values, where each i64 is a packed
 * RGBA pixel: R*16777216 + G*65536 + B*256 + A.
 *
 * Converts to SDL surface format and blits to the window surface.
 */

bool rt_sdl2_present_rgba(int64_t window_handle, SplArray* pixels,
                          int64_t width, int64_t height) {
    if (window_handle == 0 || !pixels) return false;
    if (width <= 0 || height <= 0) return false;
    if (width > INT_MAX / 4 || height > INT_MAX) return false;
    if (height > INT64_MAX / width) return false;

    SDL_Window* win = sdl2_window_get(window_handle);
    if (!win) return false;

    int64_t expected = width * height;
    if (pixels->len < expected || pixels->len < 0 || pixels->cap < pixels->len)
        return false;
    if (expected > 0 && !pixels->items) return false;
    if ((uint64_t)expected > SIZE_MAX / 4) return false;

    /* Allocate a temporary 32-bit RGBA pixel buffer */
    int64_t buf_size = width * height * 4;
    uint8_t* rgba_buf = (uint8_t*)malloc((size_t)buf_size);
    if (!rgba_buf) return false;

    /* Unpack i64 packed pixels to RGBA bytes */
    for (int64_t i = 0; i < expected; i++) {
        int64_t packed = spl_array_get_i64(pixels, i);
        rgba_buf[i * 4 + 0] = (uint8_t)((packed >> 24) & 0xFF); /* R */
        rgba_buf[i * 4 + 1] = (uint8_t)((packed >> 16) & 0xFF); /* G */
        rgba_buf[i * 4 + 2] = (uint8_t)((packed >> 8)  & 0xFF); /* B */
        rgba_buf[i * 4 + 3] = (uint8_t)((packed)       & 0xFF); /* A */
    }

    /* Create an SDL surface from the RGBA buffer */
    SDL_Surface* src = SDL_CreateRGBSurfaceFrom(
        rgba_buf,
        (int)width, (int)height,
        32,                     /* bits per pixel */
        (int)(width * 4),       /* pitch */
        0x000000FF,             /* Rmask (SDL expects masks for byte order) */
        0x0000FF00,             /* Gmask */
        0x00FF0000,             /* Bmask */
        0xFF000000              /* Amask */
    );

    if (!src) {
        free(rgba_buf);
        return false;
    }

    /*
     * NOTE: The RGBA buffer layout is R,G,B,A in memory bytes.
     * On little-endian (x86), the masks above map correctly:
     *   byte[0]=R -> 0x000000FF (least significant byte = R)
     *   byte[1]=G -> 0x0000FF00
     *   byte[2]=B -> 0x00FF0000
     *   byte[3]=A -> 0xFF000000
     */

    /* Blit to window surface */
    SDL_Surface* dst = SDL_GetWindowSurface(win);
    bool presented = false;
    if (dst) {
        /* Scale if window size differs from framebuffer size */
        SDL_Rect dst_rect = {0, 0, dst->w, dst->h};
        if (SDL_BlitScaled(src, NULL, dst, &dst_rect) == 0) {
            presented = SDL_UpdateWindowSurface(win) == 0;
        }
    }

    SDL_FreeSurface(src);
    free(rgba_buf);
    return presented;
}

/* ================================================================
 * Event Polling
 * ================================================================
 *
 * Event type codes returned by rt_sdl2_poll_event():
 *   0 = no event (queue empty)
 *   1 = quit (SDL_QUIT)
 *   2 = key down (SDL_KEYDOWN)
 *   3 = key up (SDL_KEYUP)
 *   4 = mouse motion (SDL_MOUSEMOTION)
 *   5 = mouse button down (SDL_MOUSEBUTTONDOWN)
 *   6 = mouse button up (SDL_MOUSEBUTTONUP)
 *   7 = mouse wheel (SDL_MOUSEWHEEL)
 *   8 = window event (SDL_WINDOWEVENT)
 *   9 = text input (SDL_TEXTINPUT)
 */

static int64_t rt_sdl2_event_code(void) {
    switch (g_last_event.type) {
        case SDL_QUIT:
            g_quit_requested = 1;
            return 1;
        case SDL_KEYDOWN:
            return 2;
        case SDL_KEYUP:
            return 3;
        case SDL_MOUSEMOTION:
            return 4;
        case SDL_MOUSEBUTTONDOWN:
            return 5;
        case SDL_MOUSEBUTTONUP:
            return 6;
        case SDL_MOUSEWHEEL:
            return 7;
        case SDL_WINDOWEVENT:
            return 8;
        case SDL_TEXTINPUT:
            return 9;
        default:
            return 0;
    }
}

int64_t rt_sdl2_poll_event(void) {
    SDL2_REQUIRE(0);
    while (SDL_PollEvent(&g_last_event)) {
        int64_t code;
        g_last_event_valid = 1;
        code = rt_sdl2_event_code();
        if (code != 0) return code;
    }
    g_last_event_valid = 0;
    return 0;
}

int64_t rt_sdl2_wait_event(int64_t timeout_ms) {
    SDL2_REQUIRE(0);
    int timeout = timeout_ms < 0 ? -1 :
                  timeout_ms > INT_MAX ? INT_MAX : (int)timeout_ms;
    for (;;) {
        int received = timeout < 0
            ? SDL_WaitEvent(&g_last_event)
            : SDL_WaitEventTimeout(&g_last_event, timeout);
        int64_t code;
        if (!received) {
            g_last_event_valid = 0;
            return 0;
        }
        g_last_event_valid = 1;
        code = rt_sdl2_event_code();
        if (code != 0) return code;
        timeout = 0;
    }
}

int64_t rt_sdl2_event_key_code(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_KEYDOWN || g_last_event.type == SDL_KEYUP) {
        return (int64_t)g_last_event.key.keysym.scancode;
    }
    return 0;
}

int64_t rt_sdl2_event_key_sym(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_KEYDOWN || g_last_event.type == SDL_KEYUP) {
        return (int64_t)g_last_event.key.keysym.sym;
    }
    return 0;
}

int64_t rt_sdl2_event_key_mod(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_KEYDOWN || g_last_event.type == SDL_KEYUP) {
        return (int64_t)g_last_event.key.keysym.mod;
    }
    return 0;
}

const char* rt_sdl2_event_text(void) {
    if (!g_last_event_valid) return "";
    if (g_last_event.type == SDL_TEXTINPUT) {
        return g_last_event.text.text;
    }
    return "";
}

int64_t rt_sdl2_event_mouse_x(void) {
    if (!g_last_event_valid) return 0;
    switch (g_last_event.type) {
        case SDL_MOUSEMOTION:
            return (int64_t)g_last_event.motion.x;
        case SDL_MOUSEBUTTONDOWN:
        case SDL_MOUSEBUTTONUP:
            return (int64_t)g_last_event.button.x;
        default:
            return 0;
    }
}

int64_t rt_sdl2_event_mouse_y(void) {
    if (!g_last_event_valid) return 0;
    switch (g_last_event.type) {
        case SDL_MOUSEMOTION:
            return (int64_t)g_last_event.motion.y;
        case SDL_MOUSEBUTTONDOWN:
        case SDL_MOUSEBUTTONUP:
            return (int64_t)g_last_event.button.y;
        default:
            return 0;
    }
}

int64_t rt_sdl2_event_mouse_button(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_MOUSEBUTTONDOWN ||
        g_last_event.type == SDL_MOUSEBUTTONUP) {
        /* SDL: 1=left, 2=middle, 3=right. Map to 0=left, 1=right, 2=middle */
        switch (g_last_event.button.button) {
            case SDL_BUTTON_LEFT:   return 0;
            case SDL_BUTTON_RIGHT:  return 1;
            case SDL_BUTTON_MIDDLE: return 2;
            default: return (int64_t)g_last_event.button.button;
        }
    }
    return 0;
}

int64_t rt_sdl2_event_wheel_x(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_MOUSEWHEEL) {
        return (int64_t)g_last_event.wheel.x;
    }
    return 0;
}

int64_t rt_sdl2_event_wheel_y(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_MOUSEWHEEL) {
        return (int64_t)g_last_event.wheel.y;
    }
    return 0;
}

/* ================================================================
 * Keyboard State (polled, not event-based)
 * ================================================================ */

int64_t rt_sdl2_is_key_pressed(int64_t scancode) {
    SDL2_REQUIRE(0);
    int numkeys = 0;
    const Uint8* state = SDL_GetKeyboardState(&numkeys);
    if (scancode < 0 || scancode >= numkeys) return 0;
    return (int64_t)state[scancode];
}

/* ================================================================
 * Mouse State (polled, not event-based)
 * ================================================================ */

int64_t rt_sdl2_get_mouse_x(void) {
    SDL2_REQUIRE(0);
    int x = 0, y = 0;
    SDL_GetMouseState(&x, &y);
    return (int64_t)x;
}

int64_t rt_sdl2_get_mouse_y(void) {
    SDL2_REQUIRE(0);
    int x = 0, y = 0;
    SDL_GetMouseState(&x, &y);
    return (int64_t)y;
}

int64_t rt_sdl2_is_mouse_button_pressed(int64_t button) {
    SDL2_REQUIRE(0);
    Uint32 state = SDL_GetMouseState(NULL, NULL);
    /* button: 0=left, 1=right, 2=middle (matching our event mapping) */
    switch (button) {
        case 0: return (state & SDL_BUTTON_LMASK)  ? 1 : 0;
        case 1: return (state & SDL_BUTTON_RMASK)  ? 1 : 0;
        case 2: return (state & SDL_BUTTON_MMASK)  ? 1 : 0;
        default: return 0;
    }
}

/* ================================================================
 * Time
 * ================================================================ */

int64_t rt_sdl2_get_ticks_ms(void) {
    SDL2_REQUIRE(0);
    return (int64_t)SDL_GetTicks();
}

int64_t rt_sdl2_get_ticks_ns(void) {
    SDL2_REQUIRE(0);
    if (g_perf_freq == 0) {
        g_perf_freq = SDL_GetPerformanceFrequency();
        if (g_perf_freq == 0) return 0;
    }
    uint64_t counter = SDL_GetPerformanceCounter();
    /* Convert to nanoseconds: counter * 1e9 / freq
     * Use 128-bit math to avoid overflow on large counter values */
    uint64_t seconds = counter / g_perf_freq;
    uint64_t remainder = counter % g_perf_freq;
    return (int64_t)(seconds * 1000000000ULL + remainder * 1000000000ULL / g_perf_freq);
}

/* ================================================================
 * Window State
 * ================================================================ */

int64_t rt_sdl2_window_should_close(void) {
    return g_quit_requested ? 1 : 0;
}

void rt_sdl2_clear_quit(void) {
    g_quit_requested = 0;
}

/* ================================================================
 * Window Event Details
 * ================================================================ */

int64_t rt_sdl2_event_window_event_id(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_WINDOWEVENT) {
        return (int64_t)g_last_event.window.event;
    }
    return 0;
}

int64_t rt_sdl2_event_window_data1(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_WINDOWEVENT) {
        return (int64_t)g_last_event.window.data1;
    }
    return 0;
}

int64_t rt_sdl2_event_window_data2(void) {
    if (!g_last_event_valid) return 0;
    if (g_last_event.type == SDL_WINDOWEVENT) {
        return (int64_t)g_last_event.window.data2;
    }
    return 0;
}

/* ================================================================
 * Window Properties
 * ================================================================ */

void rt_sdl2_set_window_resizable(int64_t handle, int64_t resizable) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return;
    SDL_SetWindowResizable(win, resizable ? SDL_TRUE : SDL_FALSE);
}

void rt_sdl2_set_window_fullscreen(int64_t handle, int64_t fullscreen) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return;
    SDL_SetWindowFullscreen(win, fullscreen ? SDL_WINDOW_FULLSCREEN_DESKTOP : 0);
}

int64_t rt_sdl2_set_window_fullscreen_checked(int64_t handle, int64_t fullscreen) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    return SDL_SetWindowFullscreen(win, fullscreen ? SDL_WINDOW_FULLSCREEN_DESKTOP : 0) == 0;
}

void rt_sdl2_set_window_size(int64_t handle, int64_t width, int64_t height) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win || width <= 0 || height <= 0 || width > INT_MAX || height > INT_MAX) return;
    SDL_SetWindowSize(win, (int)width, (int)height);
}

void rt_sdl2_set_window_position(int64_t handle, int64_t x, int64_t y) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win || x < INT_MIN || x > INT_MAX || y < INT_MIN || y > INT_MAX) return;
    SDL_SetWindowPosition(win, (int)x, (int)y);
}

int64_t rt_sdl2_get_window_position_x(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    int x = 0, y = 0;
    SDL_GetWindowPosition(win, &x, &y);
    return (int64_t)x;
}

int64_t rt_sdl2_get_window_position_y(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    int x = 0, y = 0;
    SDL_GetWindowPosition(win, &x, &y);
    return (int64_t)y;
}

void rt_sdl2_show_window(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return;
    SDL_ShowWindow(win);
}

void rt_sdl2_hide_window(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return;
    SDL_HideWindow(win);
}

int64_t rt_sdl2_set_window_minimum_size(int64_t handle, int64_t width, int64_t height) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win || width <= 0 || height <= 0 ||
        width > INT_MAX || height > INT_MAX) return 0;
    SDL_SetWindowMinimumSize(win, (int)width, (int)height);
    return 1;
}

int64_t rt_sdl2_set_window_maximum_size(int64_t handle, int64_t width, int64_t height) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win || width <= 0 || height <= 0 ||
        width > INT_MAX || height > INT_MAX) return 0;
    SDL_SetWindowMaximumSize(win, (int)width, (int)height);
    return 1;
}

int64_t rt_sdl2_minimize_window(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    SDL_MinimizeWindow(win);
    return 1;
}

int64_t rt_sdl2_maximize_window(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    SDL_MaximizeWindow(win);
    return 1;
}

int64_t rt_sdl2_restore_window(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    SDL_RestoreWindow(win);
    return 1;
}

int64_t rt_sdl2_set_window_bordered(int64_t handle, int64_t bordered) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    SDL_SetWindowBordered(win, bordered ? SDL_TRUE : SDL_FALSE);
    return 1;
}

int64_t rt_sdl2_set_window_always_on_top(int64_t handle, int64_t on_top) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    SDL2_REQUIRE(0);
    /*
     * Added in SDL 2.0.16. With dynamic loading this is a RUNTIME capability
     * question, not a compile-time one: an older libSDL2 simply does not
     * export the symbol, and we report that honestly instead of baking the
     * build machine's SDL version into the binary.
     */
    if (!p_SDL_SetWindowAlwaysOnTop) return 0;
    p_SDL_SetWindowAlwaysOnTop(
        win,
        on_top ? SDL_TRUE : SDL_FALSE
    );
    return 1;
}

int64_t rt_sdl2_focus_window(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return 0;
    SDL_RaiseWindow(win);
    return (SDL_GetWindowFlags(win) & SDL_WINDOW_INPUT_FOCUS) != 0;
}

int64_t rt_sdl2_window_flags(int64_t handle) {
    SDL_Window* win = sdl2_window_get(handle);
    return win ? (int64_t)SDL_GetWindowFlags(win) : 0;
}

const char* rt_sdl2_last_error(void) {
    /*
     * "the library is not installed" and "SDL failed" are different facts and
     * callers need to tell them apart, so a failed load reports the soname
     * list that was tried rather than an empty SDL_GetError().
     */
    if (!sdl2_load()) return g_sdl2_load_error;
    return SDL_GetError();
}

void rt_sdl2_set_cursor_visible(int64_t visible) {
    SDL2_REQUIRE_VOID();
    SDL_ShowCursor(visible ? SDL_ENABLE : SDL_DISABLE);
}

void rt_sdl2_set_cursor_grab(int64_t handle, int64_t grab) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win) return;
    SDL_SetWindowGrab(win, grab ? SDL_TRUE : SDL_FALSE);
}

void rt_sdl2_warp_mouse(int64_t handle, int64_t x, int64_t y) {
    SDL_Window* win = sdl2_window_get(handle);
    if (!win || x < INT_MIN || x > INT_MAX || y < INT_MIN || y > INT_MAX) return;
    SDL_WarpMouseInWindow(win, (int)x, (int)y);
}

/* ===== Clipboard ===== */

const char* rt_sdl2_clipboard_get(void) {
    SDL2_REQUIRE("");
    char* text = SDL_GetClipboardText();
    if (!text) return "";
    char* copy = strdup(text);
    SDL_free(text);
    return copy ? copy : "";
}

bool rt_sdl2_clipboard_set(const char* text) {
    SDL2_REQUIRE(false);
    return SDL_SetClipboardText(text) == 0;
}

bool rt_sdl2_clipboard_has_text(void) {
    SDL2_REQUIRE(false);
    return SDL_HasClipboardText() == SDL_TRUE;
}

/* ===== Display Info ===== */

int64_t rt_sdl2_get_num_displays(void) {
    SDL2_REQUIRE(0);
    int n = SDL_GetNumVideoDisplays();
    return n > 0 ? (int64_t)n : 0;
}

const char* rt_sdl2_get_display_name(int64_t index) {
    SDL2_REQUIRE("Unknown");
    const char* name = SDL_GetDisplayName((int)index);
    return name ? name : "Unknown";
}

int64_t rt_sdl2_get_display_bounds_x(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.x;
}

int64_t rt_sdl2_get_display_bounds_y(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.y;
}

int64_t rt_sdl2_get_display_bounds_w(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.w;
}

int64_t rt_sdl2_get_display_bounds_h(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.h;
}

double rt_sdl2_get_display_dpi(int64_t index) {
    SDL2_REQUIRE(96.0);
    float ddpi = 0.0f;
    if (SDL_GetDisplayDPI((int)index, &ddpi, NULL, NULL) != 0) return 96.0;
    return (double)ddpi;
}

int64_t rt_sdl2_get_display_usable_x(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayUsableBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.x;
}

int64_t rt_sdl2_get_display_usable_y(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayUsableBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.y;
}

int64_t rt_sdl2_get_display_usable_w(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayUsableBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.w;
}

int64_t rt_sdl2_get_display_usable_h(int64_t index) {
    SDL2_REQUIRE(0);
    SDL_Rect r;
    if (SDL_GetDisplayUsableBounds((int)index, &r) != 0) return 0;
    return (int64_t)r.h;
}

/* ===== SDL editor-facing aliases ===== */

int64_t rt_sdl_init(void) {
    return rt_sdl2_init();
}

void rt_sdl_quit(void) {
    rt_sdl2_quit();
}

int64_t rt_sdl_create_window(const char* title, int64_t width, int64_t height) {
    return rt_sdl2_create_window(title, width, height);
}

void rt_sdl_destroy_window(int64_t handle) {
    rt_sdl2_destroy_window(handle);
}

int64_t rt_sdl_get_window_width(int64_t handle) {
    return rt_sdl2_get_window_width(handle);
}

int64_t rt_sdl_get_window_height(int64_t handle) {
    return rt_sdl2_get_window_height(handle);
}

void rt_sdl_set_window_title(int64_t handle, const char* title) {
    rt_sdl2_set_window_title(handle, title);
}

bool rt_sdl_present_rgba(int64_t window_handle, SplArray* pixels, int64_t width, int64_t height) {
    return rt_sdl2_present_rgba(window_handle, pixels, width, height);
}

int64_t rt_sdl_poll_event(void) {
    return rt_sdl2_poll_event();
}

int64_t rt_sdl_event_key_sym(void) {
    return rt_sdl2_event_key_sym();
}

int64_t rt_sdl_event_key_mod(void) {
    return rt_sdl2_event_key_mod();
}

const char* rt_sdl_event_text(void) {
    return rt_sdl2_event_text();
}

int64_t rt_sdl_event_mouse_x(void) {
    return rt_sdl2_event_mouse_x();
}

int64_t rt_sdl_event_mouse_y(void) {
    return rt_sdl2_event_mouse_y();
}

int64_t rt_sdl_event_mouse_button(void) {
    return rt_sdl2_event_mouse_button();
}

int64_t rt_sdl_window_should_close(void) {
    return rt_sdl2_window_should_close();
}

void rt_sdl_clear_quit(void) {
    rt_sdl2_clear_quit();
}

int64_t rt_sdl_event_window_event_id(void) {
    return rt_sdl2_event_window_event_id();
}

int64_t rt_sdl_event_window_data1(void) {
    return rt_sdl2_event_window_data1();
}

int64_t rt_sdl_event_window_data2(void) {
    return rt_sdl2_event_window_data2();
}

#ifdef SIMPLE_SDL2_HANDLE_SELFTEST
int main(void) {
    atomic_store_explicit(&g_sdl2_owner_thread, sdl2_current_thread(), memory_order_release);
    SDL_Window *fake = (SDL_Window *)(uintptr_t)0x1234;
    int64_t first = sdl2_window_register(fake);
    if (first <= 0 || sdl2_window_get(first) != fake) return 1;
    atomic_store_explicit(&g_sdl2_owner_thread, sdl2_current_thread() ^ 1u, memory_order_release);
    if (sdl2_window_get(first) != NULL) return 2;
    atomic_store_explicit(&g_sdl2_owner_thread, sdl2_current_thread(), memory_order_release);
    if (sdl2_window_get(first + SDL2_MAX_WINDOWS) != NULL) return 3;
    if (sdl2_window_remove(first) != fake) return 4;
    if (sdl2_window_get(first) != NULL || sdl2_window_remove(first) != NULL) return 5;

    for (uintptr_t index = 0; index < SDL2_MAX_WINDOWS; index++) {
        if (sdl2_window_register((SDL_Window *)(index + 1)) <= 0) return 6;
    }
    if (sdl2_window_register((SDL_Window *)(uintptr_t)0x5678) != 0) return 7;
    return 0;
}
#endif
