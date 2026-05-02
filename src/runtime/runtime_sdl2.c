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
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_sdl2.c -o runtime_sdl2.o $(sdl2-config --cflags)
 * Link:  -lSDL2
 */

#include "runtime.h"

#include <SDL2/SDL.h>
#include <stdlib.h>
#include <string.h>

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

/* ================================================================
 * Initialization
 * ================================================================ */

int64_t rt_sdl2_init(void) {
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS) != 0) {
        fprintf(stderr, "[rt_sdl2] SDL_Init failed: %s\n", SDL_GetError());
        return 0;
    }
    g_perf_freq = SDL_GetPerformanceFrequency();
    g_quit_requested = 0;
    g_last_event_valid = 0;
    return 1;
}

void rt_sdl2_quit(void) {
    SDL_Quit();
    g_quit_requested = 0;
    g_last_event_valid = 0;
}

/* ================================================================
 * Window Management
 * ================================================================ */

int64_t rt_sdl2_create_window(const char* title, int64_t width, int64_t height) {
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
    return (int64_t)(uintptr_t)win;
}

void rt_sdl2_destroy_window(int64_t handle) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_DestroyWindow(win);
}

int64_t rt_sdl2_get_window_width(int64_t handle) {
    if (handle == 0) return 0;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    int w = 0, h = 0;
    SDL_GetWindowSize(win, &w, &h);
    return (int64_t)w;
}

int64_t rt_sdl2_get_window_height(int64_t handle) {
    if (handle == 0) return 0;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    int w = 0, h = 0;
    SDL_GetWindowSize(win, &w, &h);
    return (int64_t)h;
}

void rt_sdl2_set_window_title(int64_t handle, const char* title) {
    if (handle == 0 || !title) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
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

void rt_sdl2_present_rgba(int64_t window_handle, SplArray* pixels,
                           int64_t width, int64_t height) {
    if (window_handle == 0 || !pixels) return;
    if (width <= 0 || height <= 0) return;

    SDL_Window* win = (SDL_Window*)(uintptr_t)window_handle;

    int64_t expected = width * height;
    if (pixels->len < expected) return;

    /* Allocate a temporary 32-bit RGBA pixel buffer */
    int64_t buf_size = width * height * 4;
    uint8_t* rgba_buf = (uint8_t*)malloc((size_t)buf_size);
    if (!rgba_buf) return;

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
        return;
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
    if (dst) {
        /* Scale if window size differs from framebuffer size */
        SDL_Rect dst_rect = {0, 0, dst->w, dst->h};
        SDL_BlitScaled(src, NULL, dst, &dst_rect);
        SDL_UpdateWindowSurface(win);
    }

    SDL_FreeSurface(src);
    free(rgba_buf);
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

int64_t rt_sdl2_poll_event(void) {
    if (SDL_PollEvent(&g_last_event)) {
        g_last_event_valid = 1;

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
                /* Unknown event type — return a generic code */
                return 99;
        }
    }
    g_last_event_valid = 0;
    return 0;
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
    int numkeys = 0;
    const Uint8* state = SDL_GetKeyboardState(&numkeys);
    if (scancode < 0 || scancode >= numkeys) return 0;
    return (int64_t)state[scancode];
}

/* ================================================================
 * Mouse State (polled, not event-based)
 * ================================================================ */

int64_t rt_sdl2_get_mouse_x(void) {
    int x = 0, y = 0;
    SDL_GetMouseState(&x, &y);
    return (int64_t)x;
}

int64_t rt_sdl2_get_mouse_y(void) {
    int x = 0, y = 0;
    SDL_GetMouseState(&x, &y);
    return (int64_t)y;
}

int64_t rt_sdl2_is_mouse_button_pressed(int64_t button) {
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
    return (int64_t)SDL_GetTicks();
}

int64_t rt_sdl2_get_ticks_ns(void) {
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
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_SetWindowResizable(win, resizable ? SDL_TRUE : SDL_FALSE);
}

void rt_sdl2_set_window_fullscreen(int64_t handle, int64_t fullscreen) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_SetWindowFullscreen(win, fullscreen ? SDL_WINDOW_FULLSCREEN_DESKTOP : 0);
}

void rt_sdl2_set_window_size(int64_t handle, int64_t width, int64_t height) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_SetWindowSize(win, (int)width, (int)height);
}

void rt_sdl2_set_window_position(int64_t handle, int64_t x, int64_t y) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_SetWindowPosition(win, (int)x, (int)y);
}

int64_t rt_sdl2_get_window_position_x(int64_t handle) {
    if (handle == 0) return 0;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    int x = 0, y = 0;
    SDL_GetWindowPosition(win, &x, &y);
    return (int64_t)x;
}

int64_t rt_sdl2_get_window_position_y(int64_t handle) {
    if (handle == 0) return 0;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    int x = 0, y = 0;
    SDL_GetWindowPosition(win, &x, &y);
    return (int64_t)y;
}

void rt_sdl2_show_window(int64_t handle) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_ShowWindow(win);
}

void rt_sdl2_hide_window(int64_t handle) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_HideWindow(win);
}

void rt_sdl2_set_cursor_visible(int64_t visible) {
    SDL_ShowCursor(visible ? SDL_ENABLE : SDL_DISABLE);
}

void rt_sdl2_set_cursor_grab(int64_t handle, int64_t grab) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_SetWindowGrab(win, grab ? SDL_TRUE : SDL_FALSE);
}

void rt_sdl2_warp_mouse(int64_t handle, int64_t x, int64_t y) {
    if (handle == 0) return;
    SDL_Window* win = (SDL_Window*)(uintptr_t)handle;
    SDL_WarpMouseInWindow(win, (int)x, (int)y);
}
