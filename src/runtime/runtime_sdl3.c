/* SDL3 event runtime. Dynamically loaded; SDL2 is never substituted. */

#include "runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
static void* sdl3_open(const char* name) { return (void*)LoadLibraryA(name); }
static void* sdl3_symbol(void* lib, const char* name) {
    return lib ? (void*)GetProcAddress((HMODULE)lib, name) : NULL;
}
static void sdl3_close(void* lib) { if (lib) FreeLibrary((HMODULE)lib); }
#else
#include <dlfcn.h>
static void* sdl3_open(const char* name) { return dlopen(name, RTLD_NOW | RTLD_LOCAL); }
static void* sdl3_symbol(void* lib, const char* name) { return lib ? dlsym(lib, name) : NULL; }
static void sdl3_close(void* lib) { if (lib) dlclose(lib); }
#endif

#define SDL3_INIT_VIDEO UINT32_C(0x20)
#define SDL3_EVENT_QUIT UINT32_C(0x100)
#define SDL3_EVENT_WINDOW_RESIZED UINT32_C(0x206)
#define SDL3_EVENT_WINDOW_PIXEL_SIZE_CHANGED UINT32_C(0x207)
#define SDL3_EVENT_WINDOW_FOCUS_GAINED UINT32_C(0x20e)
#define SDL3_EVENT_WINDOW_FOCUS_LOST UINT32_C(0x20f)
#define SDL3_EVENT_WINDOW_CLOSE_REQUESTED UINT32_C(0x210)
#define SDL3_EVENT_KEY_DOWN UINT32_C(0x300)
#define SDL3_EVENT_KEY_UP UINT32_C(0x301)
#define SDL3_EVENT_TEXT_INPUT UINT32_C(0x303)
#define SDL3_EVENT_MOUSE_MOTION UINT32_C(0x400)
#define SDL3_EVENT_MOUSE_BUTTON_DOWN UINT32_C(0x401)
#define SDL3_EVENT_MOUSE_BUTTON_UP UINT32_C(0x402)
#define SDL3_EVENT_MOUSE_WHEEL UINT32_C(0x403)

#define RT_WINDOW_EVENT_NONE 0
#define RT_WINDOW_EVENT_CLOSE 1
#define RT_WINDOW_EVENT_FOCUS 2
#define RT_WINDOW_EVENT_RESIZE 3
#define RT_WINDOW_EVENT_KEY 4
#define RT_WINDOW_EVENT_TEXT 5
#define RT_WINDOW_EVENT_POINTER_MOVE 6
#define RT_WINDOW_EVENT_POINTER_BUTTON 7
#define RT_WINDOW_EVENT_WHEEL 8
#define RT_WINDOW_ACTION_RELEASE 0
#define RT_WINDOW_ACTION_PRESS 1
#define RT_WINDOW_ACTION_REPEAT 2
#define RT_SDL3_MAX_WINDOWS 16
#define RT_SDL3_HANDLE_BASE UINT64_C(4294967296)

typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
} rt_sdl3_common_event;
typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
    uint32_t window_id;
    int32_t data1, data2;
} rt_sdl3_window_event;
typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
    uint32_t window_id, which, scancode, key;
    uint16_t mod, raw;
    uint8_t down, repeat;
} rt_sdl3_keyboard_event;
typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
    uint32_t window_id;
    const char* text;
} rt_sdl3_text_event;
typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
    uint32_t window_id, which, state;
    float x, y, xrel, yrel;
} rt_sdl3_motion_event;
typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
    uint32_t window_id, which;
    uint8_t button, down, clicks, padding;
    float x, y;
} rt_sdl3_button_event;
typedef struct {
    uint32_t type, reserved;
    uint64_t timestamp;
    uint32_t window_id, which;
    float x, y;
    uint32_t direction;
    float mouse_x, mouse_y;
    int32_t integer_x, integer_y;
} rt_sdl3_wheel_event;
typedef union {
    uint8_t storage[128];
    rt_sdl3_common_event common;
    rt_sdl3_window_event window;
    rt_sdl3_keyboard_event key;
    rt_sdl3_text_event text;
    rt_sdl3_motion_event motion;
    rt_sdl3_button_event button;
    rt_sdl3_wheel_event wheel;
} rt_sdl3_event;

typedef struct { void* window; uint32_t id, generation; int live; } rt_sdl3_window_slot;
static void* g_sdl3_library;
static int g_sdl3_initialized;
static int64_t g_sdl3_sequence = 1;
static rt_sdl3_event g_sdl3_event;
static rt_sdl3_window_slot g_sdl3_windows[RT_SDL3_MAX_WINDOWS];
static char g_sdl3_text[256];

static int (*p_SDL_Init)(uint32_t);
static void (*p_SDL_Quit)(void);
static int (*p_SDL_PollEvent)(void*);
static void* (*p_SDL_CreateWindow)(const char*, int, int, uint64_t);
static void (*p_SDL_DestroyWindow)(void*);
static uint32_t (*p_SDL_GetWindowID)(void*);
static int (*p_SDL_StartTextInput)(void*);
static int (*p_SDL_StopTextInput)(void*);
static const char* (*p_SDL_GetError)(void);

#define SDL3_LOAD_REQUIRED(name) do { \
    *(void**)(&p_##name) = sdl3_symbol(g_sdl3_library, #name); \
    if (!p_##name) return 0; \
} while (0)

static int sdl3_load(void) {
    if (g_sdl3_library) return 1;
#if defined(_WIN32)
    const char* names[] = {"SDL3.dll", NULL};
#elif defined(__APPLE__)
    const char* names[] = {"libSDL3.0.dylib", "libSDL3.dylib", NULL};
#else
    const char* names[] = {"libSDL3.so.0", "libSDL3.so", NULL};
#endif
    for (int i = 0; names[i] && !g_sdl3_library; ++i) g_sdl3_library = sdl3_open(names[i]);
    if (!g_sdl3_library) return 0;
    SDL3_LOAD_REQUIRED(SDL_Init);
    SDL3_LOAD_REQUIRED(SDL_Quit);
    SDL3_LOAD_REQUIRED(SDL_PollEvent);
    SDL3_LOAD_REQUIRED(SDL_CreateWindow);
    SDL3_LOAD_REQUIRED(SDL_DestroyWindow);
    SDL3_LOAD_REQUIRED(SDL_GetWindowID);
    SDL3_LOAD_REQUIRED(SDL_StartTextInput);
    SDL3_LOAD_REQUIRED(SDL_StopTextInput);
    SDL3_LOAD_REQUIRED(SDL_GetError);
    return 1;
}

static int64_t sdl3_handle(size_t index, uint32_t generation) {
    return (int64_t)((uint64_t)generation * RT_SDL3_HANDLE_BASE + index + 1);
}
static rt_sdl3_window_slot* sdl3_slot(int64_t handle) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)handle, one = raw % RT_SDL3_HANDLE_BASE;
    uint32_t generation = (uint32_t)(raw / RT_SDL3_HANDLE_BASE);
    if (!one || one > RT_SDL3_MAX_WINDOWS) return NULL;
    rt_sdl3_window_slot* slot = &g_sdl3_windows[one - 1];
    return slot->live && slot->generation == generation ? slot : NULL;
}
static int64_t sdl3_handle_for_id(uint32_t id) {
    for (size_t i = 0; i < RT_SDL3_MAX_WINDOWS; ++i)
        if (g_sdl3_windows[i].live && g_sdl3_windows[i].id == id)
            return sdl3_handle(i, g_sdl3_windows[i].generation);
    return 0;
}

int64_t rt_sdl3_available(void) { return sdl3_load(); }
int64_t rt_sdl3_init(void) {
    if (g_sdl3_initialized) return 1;
    if (!sdl3_load() || !p_SDL_Init(SDL3_INIT_VIDEO)) return 0;
    g_sdl3_initialized = 1;
    return 1;
}
void rt_sdl3_quit(void) {
    if (g_sdl3_initialized) p_SDL_Quit();
    memset(g_sdl3_windows, 0, sizeof(g_sdl3_windows));
    g_sdl3_initialized = 0;
    g_sdl3_sequence = 1;
}
int64_t rt_sdl3_create_window(const char* title, int64_t width, int64_t height) {
    if (!g_sdl3_initialized || !title || width <= 0 || height <= 0) return 0;
    void* window = p_SDL_CreateWindow(title, (int)width, (int)height, 0);
    if (!window) return 0;
    for (size_t i = 0; i < RT_SDL3_MAX_WINDOWS; ++i) if (!g_sdl3_windows[i].live) {
        if (!g_sdl3_windows[i].generation) g_sdl3_windows[i].generation = 1;
        g_sdl3_windows[i].window = window;
        g_sdl3_windows[i].id = p_SDL_GetWindowID(window);
        g_sdl3_windows[i].live = 1;
        p_SDL_StartTextInput(window);
        return sdl3_handle(i, g_sdl3_windows[i].generation);
    }
    p_SDL_DestroyWindow(window);
    return 0;
}
int64_t rt_sdl3_destroy_window(int64_t handle) {
    rt_sdl3_window_slot* slot = sdl3_slot(handle);
    if (!slot) return 3;
    p_SDL_StopTextInput(slot->window);
    p_SDL_DestroyWindow(slot->window);
    slot->window = NULL; slot->id = 0; slot->live = 0; slot->generation += 1;
    if (!slot->generation) slot->generation = 1;
    return 0;
}
int64_t rt_sdl3_live_window_count(void) {
    int64_t count = 0;
    for (size_t i = 0; i < RT_SDL3_MAX_WINDOWS; ++i) if (g_sdl3_windows[i].live) ++count;
    return count;
}

int64_t rt_sdl3_normalize_event_type(uint32_t type) {
    switch (type) {
        case SDL3_EVENT_QUIT: case SDL3_EVENT_WINDOW_CLOSE_REQUESTED: return RT_WINDOW_EVENT_CLOSE;
        case SDL3_EVENT_WINDOW_FOCUS_GAINED: case SDL3_EVENT_WINDOW_FOCUS_LOST: return RT_WINDOW_EVENT_FOCUS;
        case SDL3_EVENT_WINDOW_RESIZED: case SDL3_EVENT_WINDOW_PIXEL_SIZE_CHANGED: return RT_WINDOW_EVENT_RESIZE;
        case SDL3_EVENT_KEY_DOWN: case SDL3_EVENT_KEY_UP: return RT_WINDOW_EVENT_KEY;
        case SDL3_EVENT_TEXT_INPUT: return RT_WINDOW_EVENT_TEXT;
        case SDL3_EVENT_MOUSE_MOTION: return RT_WINDOW_EVENT_POINTER_MOVE;
        case SDL3_EVENT_MOUSE_BUTTON_DOWN: case SDL3_EVENT_MOUSE_BUTTON_UP: return RT_WINDOW_EVENT_POINTER_BUTTON;
        case SDL3_EVENT_MOUSE_WHEEL: return RT_WINDOW_EVENT_WHEEL;
        default: return RT_WINDOW_EVENT_NONE;
    }
}

int64_t rt_sdl3_pop_event(void) {
    if (!g_sdl3_initialized) return RT_WINDOW_EVENT_NONE;
    for (;;) {
        memset(&g_sdl3_event, 0, sizeof(g_sdl3_event));
        g_sdl3_text[0] = '\0';
        if (!p_SDL_PollEvent(&g_sdl3_event)) return RT_WINDOW_EVENT_NONE;
        int64_t kind = rt_sdl3_normalize_event_type(g_sdl3_event.common.type);
        if (kind == RT_WINDOW_EVENT_TEXT) {
            if (g_sdl3_event.text.text) {
                strncpy(g_sdl3_text, g_sdl3_event.text.text, sizeof(g_sdl3_text) - 1);
                g_sdl3_text[sizeof(g_sdl3_text) - 1] = '\0';
            }
        }
        if (kind != RT_WINDOW_EVENT_NONE) return kind;
    }
}
int64_t rt_sdl3_event_window(void) {
    uint32_t id = 0;
    memcpy(&id, g_sdl3_event.storage + 16, sizeof(id));
    return sdl3_handle_for_id(id);
}
int64_t rt_sdl3_event_sequence(void) { return g_sdl3_sequence++; }
int64_t rt_sdl3_event_timestamp_ns(void) { return (int64_t)g_sdl3_event.common.timestamp; }
int64_t rt_sdl3_event_key(void) { return g_sdl3_event.key.key; }
int64_t rt_sdl3_event_scancode(void) { return g_sdl3_event.key.scancode; }
int64_t rt_sdl3_event_action(void) {
    if (g_sdl3_event.common.type == SDL3_EVENT_KEY_UP || g_sdl3_event.common.type == SDL3_EVENT_MOUSE_BUTTON_UP) return RT_WINDOW_ACTION_RELEASE;
    if (g_sdl3_event.common.type == SDL3_EVENT_KEY_DOWN && g_sdl3_event.key.repeat) return RT_WINDOW_ACTION_REPEAT;
    return RT_WINDOW_ACTION_PRESS;
}
int64_t rt_sdl3_event_modifiers(void) { return g_sdl3_event.key.mod; }
int64_t rt_sdl3_event_x_milli(void) {
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_MOTION) return (int64_t)(g_sdl3_event.motion.x * 1000.0f);
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_BUTTON_DOWN || g_sdl3_event.common.type == SDL3_EVENT_MOUSE_BUTTON_UP) return (int64_t)(g_sdl3_event.button.x * 1000.0f);
    return 0;
}
int64_t rt_sdl3_event_y_milli(void) {
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_MOTION) return (int64_t)(g_sdl3_event.motion.y * 1000.0f);
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_BUTTON_DOWN || g_sdl3_event.common.type == SDL3_EVENT_MOUSE_BUTTON_UP) return (int64_t)(g_sdl3_event.button.y * 1000.0f);
    return 0;
}
int64_t rt_sdl3_event_dx_milli(void) {
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_MOTION) return (int64_t)(g_sdl3_event.motion.xrel * 1000.0f);
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_WHEEL) return (int64_t)(g_sdl3_event.wheel.x * 1000.0f);
    return 0;
}
int64_t rt_sdl3_event_dy_milli(void) {
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_MOTION) return (int64_t)(g_sdl3_event.motion.yrel * 1000.0f);
    if (g_sdl3_event.common.type == SDL3_EVENT_MOUSE_WHEEL) return (int64_t)(g_sdl3_event.wheel.y * 1000.0f);
    return 0;
}
int64_t rt_sdl3_event_width(void) { return g_sdl3_event.window.data1; }
int64_t rt_sdl3_event_height(void) { return g_sdl3_event.window.data2; }
const char* rt_sdl3_event_text(void) { return g_sdl3_text; }
const char* rt_sdl3_last_error(void) { return p_SDL_GetError ? p_SDL_GetError() : "SDL3 unavailable"; }

/* Explicit cleanup for runtime unload tests; normal process shutdown may omit it. */
void rt_sdl3_unload(void) { rt_sdl3_quit(); sdl3_close(g_sdl3_library); g_sdl3_library = NULL; }
