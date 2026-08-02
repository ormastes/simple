/*
 * Simple GLFW runtime.
 *
 * GLFW is loaded at runtime so builds remain portable. Missing GLFW or OpenGL
 * symbols fail closed; no other backend is substituted.
 */

#include "runtime.h"

#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(_WIN32)
#include <windows.h>
static void* glfw_open_library(const char* name) { return (void*)LoadLibraryA(name); }
static void* glfw_load_symbol(void* lib, const char* name) { return lib ? (void*)GetProcAddress((HMODULE)lib, name) : NULL; }
static void glfw_close_library(void* lib) { if (lib) FreeLibrary((HMODULE)lib); }
#else
#include <dlfcn.h>
static void* glfw_open_library(const char* name) { return dlopen(name, RTLD_NOW | RTLD_LOCAL); }
static void* glfw_load_symbol(void* lib, const char* name) { return lib ? dlsym(lib, name) : NULL; }
static void glfw_close_library(void* lib) { if (lib) dlclose(lib); }
#endif

typedef struct GLFWwindow GLFWwindow;
typedef void (*rt_glfw_key_fn)(GLFWwindow*, int, int, int, int);
typedef void (*rt_glfw_char_fn)(GLFWwindow*, unsigned int);
typedef void (*rt_glfw_cursor_fn)(GLFWwindow*, double, double);
typedef void (*rt_glfw_button_fn)(GLFWwindow*, int, int, int);
typedef void (*rt_glfw_scroll_fn)(GLFWwindow*, double, double);
typedef void (*rt_glfw_focus_fn)(GLFWwindow*, int);
typedef void (*rt_glfw_size_fn)(GLFWwindow*, int, int);
typedef void (*rt_glfw_close_fn)(GLFWwindow*);

#define RT_GLFW_MAX_WINDOWS 16
#define RT_GLFW_MAX_EVENTS 256
#define RT_GLFW_HANDLE_BASE UINT64_C(4294967296)

#define GLFW_CONTEXT_VERSION_MAJOR 0x00022002
#define GLFW_CONTEXT_VERSION_MINOR 0x00022003
#define GLFW_PRESS 1
#define GLFW_REPEAT 2

#define GL_COLOR_BUFFER_BIT 0x00004000
#define GL_QUADS 0x0007
#define GL_TEXTURE_2D 0x0DE1
#define GL_TEXTURE_MAG_FILTER 0x2800
#define GL_TEXTURE_MIN_FILTER 0x2801
#define GL_NEAREST 0x2600
#define GL_RGBA8 0x8058
#define GL_BGRA 0x80E1
#define GL_UNSIGNED_BYTE 0x1401

typedef struct {
    GLFWwindow* window;
    uint32_t generation;
    int live;
    int64_t frame_sequence;
    uint32_t* pixels;
    size_t pixel_capacity;
    int64_t buffer_growth_count;
    unsigned int texture;
    int texture_width;
    int texture_height;
} rt_glfw_window_slot;

typedef struct {
    int64_t kind;
    int64_t window_handle;
    int64_t sequence;
    int64_t timestamp_ns;
    int64_t key;
    int64_t scancode;
    int64_t action;
    int64_t modifiers;
    int64_t x_milli;
    int64_t y_milli;
    int64_t delta_x_milli;
    int64_t delta_y_milli;
    int64_t width;
    int64_t height;
    char text[8];
} rt_glfw_event;

static void* g_glfw_library;
static int g_glfw_initialized;
static int64_t g_glfw_sequence = 1;
static int64_t g_glfw_dropped_events;
static rt_glfw_window_slot g_glfw_windows[RT_GLFW_MAX_WINDOWS];
static rt_glfw_event g_glfw_events[RT_GLFW_MAX_EVENTS];
static size_t g_glfw_event_head;
static size_t g_glfw_event_count;
static rt_glfw_event g_glfw_last_event;

static int (*p_glfwInit)(void);
static void (*p_glfwTerminate)(void);
static void (*p_glfwWindowHint)(int, int);
static GLFWwindow* (*p_glfwCreateWindow)(
    int, int, const char*, void*, GLFWwindow*
);
static void (*p_glfwDestroyWindow)(GLFWwindow*);
static void (*p_glfwMakeContextCurrent)(GLFWwindow*);
static void (*p_glfwSwapInterval)(int);
static void (*p_glfwSwapBuffers)(GLFWwindow*);
static void (*p_glfwPollEvents)(void);
static int (*p_glfwWindowShouldClose)(GLFWwindow*);
static void (*p_glfwSetWindowShouldClose)(GLFWwindow*, int);
static void (*p_glfwGetWindowSize)(GLFWwindow*, int*, int*);
static void (*p_glfwGetFramebufferSize)(GLFWwindow*, int*, int*);
static void (*p_glfwGetCursorPos)(GLFWwindow*, double*, double*);
static void* (*p_glfwGetProcAddress)(const char*);
static void (*p_glfwShowWindow)(GLFWwindow*);
static void (*p_glfwHideWindow)(GLFWwindow*);
static void (*p_glfwFocusWindow)(GLFWwindow*);
static void (*p_glfwIconifyWindow)(GLFWwindow*);
static void (*p_glfwMaximizeWindow)(GLFWwindow*);
static void (*p_glfwRestoreWindow)(GLFWwindow*);
static void (*p_glfwGetWindowContentScale)(GLFWwindow*, float*, float*);
static rt_glfw_key_fn (*p_glfwSetKeyCallback)(GLFWwindow*, rt_glfw_key_fn);
static rt_glfw_char_fn (*p_glfwSetCharCallback)(GLFWwindow*, rt_glfw_char_fn);
static rt_glfw_cursor_fn (*p_glfwSetCursorPosCallback)(GLFWwindow*, rt_glfw_cursor_fn);
static rt_glfw_button_fn (*p_glfwSetMouseButtonCallback)(GLFWwindow*, rt_glfw_button_fn);
static rt_glfw_scroll_fn (*p_glfwSetScrollCallback)(GLFWwindow*, rt_glfw_scroll_fn);
static rt_glfw_focus_fn (*p_glfwSetWindowFocusCallback)(GLFWwindow*, rt_glfw_focus_fn);
static rt_glfw_size_fn (*p_glfwSetFramebufferSizeCallback)(GLFWwindow*, rt_glfw_size_fn);
static rt_glfw_close_fn (*p_glfwSetWindowCloseCallback)(GLFWwindow*, rt_glfw_close_fn);
static const char* (*p_glfwGetClipboardString)(GLFWwindow*);
static void (*p_glfwSetClipboardString)(GLFWwindow*, const char*);

static void (*p_glViewport)(int, int, int, int);
static void (*p_glClearColor)(float, float, float, float);
static void (*p_glClear)(unsigned int);
static void (*p_glGenTextures)(int, unsigned int*);
static void (*p_glDeleteTextures)(int, const unsigned int*);
static void (*p_glBindTexture)(unsigned int, unsigned int);
static void (*p_glTexParameteri)(unsigned int, unsigned int, int);
static void (*p_glTexImage2D)(
    unsigned int, int, int, int, int, int, unsigned int, unsigned int,
    const void*
);
static void (*p_glTexSubImage2D)(
    unsigned int, int, int, int, int, int, unsigned int, unsigned int,
    const void*
);
static void (*p_glEnable)(unsigned int);
static void (*p_glDisable)(unsigned int);
static void (*p_glBegin)(unsigned int);
static void (*p_glEnd)(void);
static void (*p_glTexCoord2f)(float, float);
static void (*p_glVertex2f)(float, float);

static void* glfw_symbol(const char* name) {
    return glfw_load_symbol(g_glfw_library, name);
}

#define LOAD_REQUIRED(name) do { \
    *(void**)(&p_##name) = glfw_symbol(#name); \
    if (!p_##name) return 0; \
} while (0)

#define LOAD_OPTIONAL(name) \
    *(void**)(&p_##name) = glfw_symbol(#name)

static int64_t glfw_now_ns(void) {
#if defined(_WIN32)
    LARGE_INTEGER counter, frequency;
    if (!QueryPerformanceCounter(&counter) || !QueryPerformanceFrequency(&frequency) || frequency.QuadPart <= 0) return 0;
    return (int64_t)((counter.QuadPart / frequency.QuadPart) * INT64_C(1000000000) +
        ((counter.QuadPart % frequency.QuadPart) * INT64_C(1000000000)) / frequency.QuadPart);
#else
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * INT64_C(1000000000) + ts.tv_nsec;
#endif
}

static int64_t glfw_handle(size_t index, uint32_t generation) {
    return (int64_t)((uint64_t)generation * RT_GLFW_HANDLE_BASE + index + 1);
}

static rt_glfw_window_slot* glfw_slot(int64_t handle) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)handle;
    uint64_t one_based = raw % RT_GLFW_HANDLE_BASE;
    uint32_t generation = (uint32_t)(raw / RT_GLFW_HANDLE_BASE);
    if (one_based == 0 || one_based > RT_GLFW_MAX_WINDOWS || generation == 0) {
        return NULL;
    }
    rt_glfw_window_slot* slot = &g_glfw_windows[one_based - 1];
    if (!slot->live || slot->generation != generation || !slot->window) {
        return NULL;
    }
    return slot;
}

static int64_t glfw_handle_for_window(GLFWwindow* window) {
    size_t i;
    for (i = 0; i < RT_GLFW_MAX_WINDOWS; ++i) {
        if (g_glfw_windows[i].live && g_glfw_windows[i].window == window) {
            return glfw_handle(i, g_glfw_windows[i].generation);
        }
    }
    return 0;
}

static void glfw_push_event(rt_glfw_event event) {
    event.sequence = g_glfw_sequence++;
    event.timestamp_ns = glfw_now_ns();
    if (g_glfw_event_count == RT_GLFW_MAX_EVENTS) {
        g_glfw_dropped_events += 1;
        return;
    }
    size_t tail = (g_glfw_event_head + g_glfw_event_count) %
        RT_GLFW_MAX_EVENTS;
    g_glfw_events[tail] = event;
    g_glfw_event_count += 1;
}

static void glfw_drop_window_events(int64_t window_handle) {
    rt_glfw_event kept[RT_GLFW_MAX_EVENTS];
    size_t kept_count = 0;
    size_t i;
    for (i = 0; i < g_glfw_event_count; ++i) {
        size_t index = (g_glfw_event_head + i) % RT_GLFW_MAX_EVENTS;
        if (g_glfw_events[index].window_handle != window_handle) {
            kept[kept_count++] = g_glfw_events[index];
        }
    }
    if (kept_count > 0) {
        memcpy(g_glfw_events, kept, kept_count * sizeof(rt_glfw_event));
    }
    g_glfw_event_head = 0;
    g_glfw_event_count = kept_count;
}

static rt_glfw_event glfw_event(int64_t kind, GLFWwindow* window) {
    rt_glfw_event event;
    memset(&event, 0, sizeof(event));
    event.kind = kind;
    event.window_handle = glfw_handle_for_window(window);
    return event;
}

static void glfw_key_callback(
    GLFWwindow* window, int key, int scancode, int action, int mods
) {
    rt_glfw_event event = glfw_event(4, window);
    event.key = key;
    event.scancode = scancode;
    event.action = action;
    event.modifiers = mods & 15;
    glfw_push_event(event);
}

static void glfw_char_callback(GLFWwindow* window, unsigned int codepoint) {
    rt_glfw_event event = glfw_event(5, window);
    if (codepoint <= 0x7F) {
        event.text[0] = (char)codepoint;
    } else if (codepoint <= 0x7FF) {
        event.text[0] = (char)(0xC0 | (codepoint >> 6));
        event.text[1] = (char)(0x80 | (codepoint & 0x3F));
    } else if (codepoint <= 0xFFFF) {
        event.text[0] = (char)(0xE0 | (codepoint >> 12));
        event.text[1] = (char)(0x80 | ((codepoint >> 6) & 0x3F));
        event.text[2] = (char)(0x80 | (codepoint & 0x3F));
    } else if (codepoint <= 0x10FFFF) {
        event.text[0] = (char)(0xF0 | (codepoint >> 18));
        event.text[1] = (char)(0x80 | ((codepoint >> 12) & 0x3F));
        event.text[2] = (char)(0x80 | ((codepoint >> 6) & 0x3F));
        event.text[3] = (char)(0x80 | (codepoint & 0x3F));
    } else {
        return;
    }
    glfw_push_event(event);
}

static void glfw_cursor_callback(GLFWwindow* window, double x, double y) {
    rt_glfw_event event = glfw_event(6, window);
    event.x_milli = (int64_t)(x * 1000.0);
    event.y_milli = (int64_t)(y * 1000.0);
    glfw_push_event(event);
}

static void glfw_button_callback(
    GLFWwindow* window, int button, int action, int mods
) {
    rt_glfw_event event = glfw_event(7, window);
    double x = 0.0, y = 0.0;
    p_glfwGetCursorPos(window, &x, &y);
    event.key = button;
    event.action = action;
    event.modifiers = mods & 15;
    event.x_milli = (int64_t)(x * 1000.0);
    event.y_milli = (int64_t)(y * 1000.0);
    glfw_push_event(event);
}

static void glfw_scroll_callback(GLFWwindow* window, double x, double y) {
    rt_glfw_event event = glfw_event(8, window);
    event.delta_x_milli = (int64_t)(x * 1000.0);
    event.delta_y_milli = (int64_t)(y * 1000.0);
    glfw_push_event(event);
}

static void glfw_focus_callback(GLFWwindow* window, int focused) {
    rt_glfw_event event = glfw_event(2, window);
    event.action = focused ? GLFW_PRESS : 0;
    glfw_push_event(event);
}

static void glfw_resize_callback(GLFWwindow* window, int width, int height) {
    rt_glfw_event event = glfw_event(3, window);
    event.width = width;
    event.height = height;
    glfw_push_event(event);
}

static void glfw_close_callback(GLFWwindow* window) {
    glfw_push_event(glfw_event(1, window));
}

static int glfw_load(void) {
#if defined(_WIN32)
    const char* names[] = {"glfw3.dll", "glfw.dll", NULL};
#elif defined(__APPLE__)
    const char* names[] = {"libglfw.3.dylib", "libglfw.dylib", NULL};
#else
    const char* names[] = {"libglfw.so.3", "libglfw.so", NULL};
#endif
    for (int i = 0; names[i] && !g_glfw_library; ++i) g_glfw_library = glfw_open_library(names[i]);
    if (!g_glfw_library) return 0;
    LOAD_REQUIRED(glfwInit);
    LOAD_REQUIRED(glfwTerminate);
    LOAD_REQUIRED(glfwWindowHint);
    LOAD_REQUIRED(glfwCreateWindow);
    LOAD_REQUIRED(glfwDestroyWindow);
    LOAD_REQUIRED(glfwMakeContextCurrent);
    LOAD_REQUIRED(glfwSwapInterval);
    LOAD_REQUIRED(glfwSwapBuffers);
    LOAD_REQUIRED(glfwPollEvents);
    LOAD_REQUIRED(glfwWindowShouldClose);
    LOAD_REQUIRED(glfwSetWindowShouldClose);
    LOAD_REQUIRED(glfwGetWindowSize);
    LOAD_REQUIRED(glfwGetFramebufferSize);
    LOAD_REQUIRED(glfwGetCursorPos);
    LOAD_REQUIRED(glfwGetProcAddress);
    LOAD_REQUIRED(glfwSetKeyCallback);
    LOAD_REQUIRED(glfwSetCharCallback);
    LOAD_REQUIRED(glfwSetCursorPosCallback);
    LOAD_REQUIRED(glfwSetMouseButtonCallback);
    LOAD_REQUIRED(glfwSetScrollCallback);
    LOAD_REQUIRED(glfwSetWindowFocusCallback);
    LOAD_REQUIRED(glfwSetFramebufferSizeCallback);
    LOAD_REQUIRED(glfwSetWindowCloseCallback);
    LOAD_OPTIONAL(glfwShowWindow);
    LOAD_OPTIONAL(glfwHideWindow);
    LOAD_OPTIONAL(glfwFocusWindow);
    LOAD_OPTIONAL(glfwIconifyWindow);
    LOAD_OPTIONAL(glfwMaximizeWindow);
    LOAD_OPTIONAL(glfwRestoreWindow);
    LOAD_OPTIONAL(glfwGetWindowContentScale);
    LOAD_OPTIONAL(glfwGetClipboardString);
    LOAD_OPTIONAL(glfwSetClipboardString);
    return 1;
}

int64_t rt_glfw_init(void) {
    if (g_glfw_initialized) return 1;
    if (!glfw_load() || !p_glfwInit()) {
        glfw_close_library(g_glfw_library);
        g_glfw_library = NULL;
        return 0;
    }
    g_glfw_initialized = 1;
    return 1;
}

void rt_glfw_terminate(void) {
    if (!g_glfw_initialized) return;
    size_t i;
    for (i = 0; i < RT_GLFW_MAX_WINDOWS; ++i) {
        if (g_glfw_windows[i].live) {
            p_glfwMakeContextCurrent(g_glfw_windows[i].window);
            if (g_glfw_windows[i].texture && p_glDeleteTextures) {
                p_glDeleteTextures(1, &g_glfw_windows[i].texture);
            }
            free(g_glfw_windows[i].pixels);
            p_glfwDestroyWindow(g_glfw_windows[i].window);
            g_glfw_windows[i].window = NULL;
            g_glfw_windows[i].live = 0;
            g_glfw_windows[i].pixels = NULL;
            g_glfw_windows[i].pixel_capacity = 0;
            g_glfw_windows[i].buffer_growth_count = 0;
            g_glfw_windows[i].texture = 0;
            g_glfw_windows[i].texture_width = 0;
            g_glfw_windows[i].texture_height = 0;
            g_glfw_windows[i].generation += 1;
        }
    }
    p_glfwTerminate();
    g_glfw_initialized = 0;
    g_glfw_event_head = 0;
    g_glfw_event_count = 0;
    glfw_close_library(g_glfw_library);
    g_glfw_library = NULL;
}

int64_t rt_glfw_create_window(const char* title, int64_t width, int64_t height) {
    if (!g_glfw_initialized || width <= 0 || height <= 0) return 0;
    p_glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 2);
    p_glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 1);
    GLFWwindow* window = p_glfwCreateWindow(
        (int)width, (int)height, title ? title : "Simple Window", NULL, NULL
    );
    if (!window) return 0;
    size_t i;
    for (i = 0; i < RT_GLFW_MAX_WINDOWS; ++i) {
        if (!g_glfw_windows[i].live) {
            if (g_glfw_windows[i].generation == 0) {
                g_glfw_windows[i].generation = 1;
            }
            g_glfw_windows[i].window = window;
            g_glfw_windows[i].frame_sequence = 0;
            g_glfw_windows[i].pixels = NULL;
            g_glfw_windows[i].pixel_capacity = 0;
            g_glfw_windows[i].buffer_growth_count = 0;
            g_glfw_windows[i].texture = 0;
            g_glfw_windows[i].texture_width = 0;
            g_glfw_windows[i].texture_height = 0;
            p_glfwMakeContextCurrent(window);
            p_glfwSwapInterval(1);
            p_glViewport = (void(*)(int,int,int,int))
                p_glfwGetProcAddress("glViewport");
            p_glClearColor = (void(*)(float,float,float,float))
                p_glfwGetProcAddress("glClearColor");
            p_glClear = (void(*)(unsigned int))
                p_glfwGetProcAddress("glClear");
            p_glGenTextures = (void(*)(int,unsigned int*))
                p_glfwGetProcAddress("glGenTextures");
            p_glDeleteTextures = (void(*)(int,const unsigned int*))
                p_glfwGetProcAddress("glDeleteTextures");
            p_glBindTexture = (void(*)(unsigned int,unsigned int))
                p_glfwGetProcAddress("glBindTexture");
            p_glTexParameteri = (void(*)(unsigned int,unsigned int,int))
                p_glfwGetProcAddress("glTexParameteri");
            p_glTexImage2D = (void(*)(unsigned int,int,int,int,int,int,
                unsigned int,unsigned int,const void*))
                p_glfwGetProcAddress("glTexImage2D");
            p_glTexSubImage2D = (void(*)(unsigned int,int,int,int,int,int,
                unsigned int,unsigned int,const void*))
                p_glfwGetProcAddress("glTexSubImage2D");
            p_glEnable = (void(*)(unsigned int))
                p_glfwGetProcAddress("glEnable");
            p_glDisable = (void(*)(unsigned int))
                p_glfwGetProcAddress("glDisable");
            p_glBegin = (void(*)(unsigned int))
                p_glfwGetProcAddress("glBegin");
            p_glEnd = (void(*)(void))
                p_glfwGetProcAddress("glEnd");
            p_glTexCoord2f = (void(*)(float,float))
                p_glfwGetProcAddress("glTexCoord2f");
            p_glVertex2f = (void(*)(float,float))
                p_glfwGetProcAddress("glVertex2f");
            if (!p_glViewport || !p_glClearColor || !p_glClear ||
                !p_glGenTextures || !p_glDeleteTextures || !p_glBindTexture ||
                !p_glTexParameteri || !p_glTexImage2D ||
                !p_glTexSubImage2D || !p_glEnable || !p_glDisable ||
                !p_glBegin || !p_glEnd || !p_glTexCoord2f || !p_glVertex2f) {
                p_glfwDestroyWindow(window);
                g_glfw_windows[i].window = NULL;
                return 0;
            }
            p_glGenTextures(1, &g_glfw_windows[i].texture);
            if (!g_glfw_windows[i].texture) {
                p_glfwDestroyWindow(window);
                g_glfw_windows[i].window = NULL;
                return 0;
            }
            p_glBindTexture(GL_TEXTURE_2D, g_glfw_windows[i].texture);
            p_glTexParameteri(
                GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST
            );
            p_glTexParameteri(
                GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST
            );
            g_glfw_windows[i].live = 1;
            p_glfwSetKeyCallback(window, glfw_key_callback);
            p_glfwSetCharCallback(window, glfw_char_callback);
            p_glfwSetCursorPosCallback(window, glfw_cursor_callback);
            p_glfwSetMouseButtonCallback(window, glfw_button_callback);
            p_glfwSetScrollCallback(window, glfw_scroll_callback);
            p_glfwSetWindowFocusCallback(window, glfw_focus_callback);
            p_glfwSetFramebufferSizeCallback(window, glfw_resize_callback);
            p_glfwSetWindowCloseCallback(window, glfw_close_callback);
            return glfw_handle(i, g_glfw_windows[i].generation);
        }
    }
    p_glfwDestroyWindow(window);
    return 0;
}

int64_t rt_glfw_destroy_window(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    p_glfwMakeContextCurrent(slot->window);
    if (slot->texture) p_glDeleteTextures(1, &slot->texture);
    free(slot->pixels);
    p_glfwDestroyWindow(slot->window);
    glfw_drop_window_events(handle);
    slot->window = NULL;
    slot->live = 0;
    slot->frame_sequence = 0;
    slot->pixels = NULL;
    slot->pixel_capacity = 0;
    slot->buffer_growth_count = 0;
    slot->texture = 0;
    slot->texture_width = 0;
    slot->texture_height = 0;
    slot->generation += 1;
    if (slot->generation == 0) slot->generation = 1;
    return 0;
}

static int64_t glfw_stage_capacity(
    rt_glfw_window_slot* slot, int64_t count
) {
    if ((size_t)count > slot->pixel_capacity) {
        uint32_t* grown = realloc(
            slot->pixels, (size_t)count * sizeof(uint32_t)
        );
        if (!grown) return 6;
        slot->pixels = grown;
        slot->pixel_capacity = (size_t)count;
        slot->buffer_growth_count += 1;
    }
    return 0;
}

static int64_t glfw_present_staged(
    rt_glfw_window_slot* slot, int64_t width, int64_t height
) {
    int framebuffer_width = 0, framebuffer_height = 0;
    p_glfwMakeContextCurrent(slot->window);
    p_glfwGetFramebufferSize(
        slot->window, &framebuffer_width, &framebuffer_height
    );
    if (framebuffer_width <= 0 || framebuffer_height <= 0) return 5;
    p_glViewport(0, 0, framebuffer_width, framebuffer_height);
    p_glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
    p_glClear(GL_COLOR_BUFFER_BIT);
    p_glEnable(GL_TEXTURE_2D);
    p_glBindTexture(GL_TEXTURE_2D, slot->texture);
    if (slot->texture_width != (int)width ||
        slot->texture_height != (int)height) {
        p_glTexImage2D(
            GL_TEXTURE_2D, 0, GL_RGBA8, (int)width, (int)height, 0,
            GL_BGRA, GL_UNSIGNED_BYTE, slot->pixels
        );
        slot->texture_width = (int)width;
        slot->texture_height = (int)height;
    } else {
        p_glTexSubImage2D(
            GL_TEXTURE_2D, 0, 0, 0, (int)width, (int)height,
            GL_BGRA, GL_UNSIGNED_BYTE, slot->pixels
        );
    }
    p_glBegin(GL_QUADS);
    p_glTexCoord2f(0.0f, 0.0f); p_glVertex2f(-1.0f, 1.0f);
    p_glTexCoord2f(1.0f, 0.0f); p_glVertex2f(1.0f, 1.0f);
    p_glTexCoord2f(1.0f, 1.0f); p_glVertex2f(1.0f, -1.0f);
    p_glTexCoord2f(0.0f, 1.0f); p_glVertex2f(-1.0f, -1.0f);
    p_glEnd();
    p_glDisable(GL_TEXTURE_2D);
    p_glfwSwapBuffers(slot->window);
    slot->frame_sequence += 1;
    return 0;
}

static int64_t glfw_validate_frame(
    int64_t width, int64_t height, int64_t pixel_count
) {
    if (width <= 0 || height <= 0 || width > INT_MAX ||
        height > INT_MAX || width > INT64_MAX / height) return 5;
    int64_t expected = width * height;
    if (pixel_count != expected ||
        (uint64_t)expected > SIZE_MAX / sizeof(uint32_t)) return 5;
    return 0;
}

int64_t rt_glfw_present_argb(
    int64_t handle, SplArray* pixels, int64_t width, int64_t height
) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (!pixels) return 5;
    int64_t status = glfw_validate_frame(width, height, pixels->len);
    if (status != 0) return status;
    status = glfw_stage_capacity(slot, pixels->len);
    if (status != 0) return status;
    int64_t i;
    for (i = 0; i < pixels->len; ++i) {
        slot->pixels[i] = (uint32_t)spl_array_get_i64(pixels, i);
    }
    return glfw_present_staged(slot, width, height);
}

int64_t rt_glfw_present_argb_words_raw(
    int64_t handle,
    int64_t pixels_addr,
    int64_t pixel_count,
    int64_t width,
    int64_t height
) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (pixels_addr <= 0 || (pixels_addr & 3) != 0) return 5;
    int64_t status = glfw_validate_frame(width, height, pixel_count);
    if (status != 0) return status;
    status = glfw_stage_capacity(slot, pixel_count);
    if (status != 0) return status;
    const uint32_t* pixels = (const uint32_t*)(uintptr_t)pixels_addr;
    int64_t i;
    for (i = 0; i < pixel_count; ++i) {
        slot->pixels[i] = pixels[i];
    }
    return glfw_present_staged(slot, width, height);
}

int64_t rt_glfw_pump_events(void) {
    if (!g_glfw_initialized) return 0;
    p_glfwPollEvents();
    return 1;
}

int64_t rt_glfw_pop_event(void) {
    if (!g_glfw_initialized) return 0;
    if (g_glfw_event_count == 0) return 0;
    g_glfw_last_event = g_glfw_events[g_glfw_event_head];
    g_glfw_event_head = (g_glfw_event_head + 1) % RT_GLFW_MAX_EVENTS;
    g_glfw_event_count -= 1;
    return g_glfw_last_event.kind;
}

int64_t rt_glfw_poll_event(void) {
    rt_glfw_pump_events();
    return rt_glfw_pop_event();
}

int64_t rt_glfw_event_window(void) { return g_glfw_last_event.window_handle; }
int64_t rt_glfw_event_sequence(void) { return g_glfw_last_event.sequence; }
int64_t rt_glfw_event_timestamp_ns(void) { return g_glfw_last_event.timestamp_ns; }
int64_t rt_glfw_event_key(void) { return g_glfw_last_event.key; }
int64_t rt_glfw_event_scancode(void) { return g_glfw_last_event.scancode; }
int64_t rt_glfw_event_action(void) { return g_glfw_last_event.action; }
int64_t rt_glfw_event_modifiers(void) { return g_glfw_last_event.modifiers; }
int64_t rt_glfw_event_x_milli(void) { return g_glfw_last_event.x_milli; }
int64_t rt_glfw_event_y_milli(void) { return g_glfw_last_event.y_milli; }
int64_t rt_glfw_event_dx_milli(void) { return g_glfw_last_event.delta_x_milli; }
int64_t rt_glfw_event_dy_milli(void) { return g_glfw_last_event.delta_y_milli; }
int64_t rt_glfw_event_width(void) { return g_glfw_last_event.width; }
int64_t rt_glfw_event_height(void) { return g_glfw_last_event.height; }
const char* rt_glfw_event_text(void) { return g_glfw_last_event.text; }
int64_t rt_glfw_dropped_event_count(void) { return g_glfw_dropped_events; }
int64_t rt_glfw_queued_event_count(void) {
    return (int64_t)g_glfw_event_count;
}
int64_t rt_glfw_live_window_count(void) {
    int64_t count = 0;
    size_t i;
    for (i = 0; i < RT_GLFW_MAX_WINDOWS; ++i) {
        if (g_glfw_windows[i].live) count += 1;
    }
    return count;
}

int64_t rt_glfw_should_close(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    return slot ? p_glfwWindowShouldClose(slot->window) : 1;
}

int64_t rt_glfw_set_visible(int64_t handle, int64_t visible) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (visible && p_glfwShowWindow) p_glfwShowWindow(slot->window);
    else if (!visible && p_glfwHideWindow) p_glfwHideWindow(slot->window);
    else return 2;
    return 0;
}

int64_t rt_glfw_focus(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (!p_glfwFocusWindow) return 2;
    p_glfwFocusWindow(slot->window);
    return 0;
}

int64_t rt_glfw_minimize(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (!p_glfwIconifyWindow) return 2;
    p_glfwIconifyWindow(slot->window);
    return 0;
}

int64_t rt_glfw_maximize(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (!p_glfwMaximizeWindow) return 2;
    p_glfwMaximizeWindow(slot->window);
    return 0;
}

int64_t rt_glfw_restore(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (!p_glfwRestoreWindow) return 2;
    p_glfwRestoreWindow(slot->window);
    return 0;
}

int64_t rt_glfw_framebuffer_width(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    int width = 0, height = 0;
    if (slot) p_glfwGetFramebufferSize(slot->window, &width, &height);
    return width;
}

int64_t rt_glfw_window_width(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    int width = 0, height = 0;
    if (slot) p_glfwGetWindowSize(slot->window, &width, &height);
    return width;
}

int64_t rt_glfw_window_height(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    int width = 0, height = 0;
    if (slot) p_glfwGetWindowSize(slot->window, &width, &height);
    return height;
}

int64_t rt_glfw_framebuffer_height(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    int width = 0, height = 0;
    if (slot) p_glfwGetFramebufferSize(slot->window, &width, &height);
    return height;
}

int64_t rt_glfw_content_scale_milli(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot || !p_glfwGetWindowContentScale) return 0;
    float x = 0.0f, y = 0.0f;
    p_glfwGetWindowContentScale(slot->window, &x, &y);
    return (int64_t)(x * 1000.0f);
}

int64_t rt_glfw_frame_sequence(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    return slot ? slot->frame_sequence : 0;
}

int64_t rt_glfw_buffer_growth_count(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    return slot ? slot->buffer_growth_count : 0;
}

const char* rt_glfw_clipboard_get(int64_t handle) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot || !p_glfwGetClipboardString) return "";
    const char* text = p_glfwGetClipboardString(slot->window);
    return text ? text : "";
}

int64_t rt_glfw_clipboard_set(int64_t handle, const char* text) {
    rt_glfw_window_slot* slot = glfw_slot(handle);
    if (!slot) return 3;
    if (!p_glfwSetClipboardString) return 2;
    p_glfwSetClipboardString(slot->window, text ? text : "");
    return 0;
}
