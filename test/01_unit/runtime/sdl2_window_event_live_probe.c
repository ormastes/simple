#include "runtime.h"

#include <SDL.h>
#include <assert.h>
#include <string.h>

int main(void) {
    SDL_Event event;
    int64_t window;

    assert(rt_sdl2_init() == 1);
    window = rt_sdl2_create_window("sdl2-contract", 160, 90);
    assert(window != 0);
    assert((rt_sdl2_window_flags(window) & SDL_WINDOW_SHOWN) != 0);
    assert(rt_sdl2_set_window_minimum_size(window, 80, 45) == 1);
    assert(rt_sdl2_set_window_maximum_size(window, 320, 180) == 1);
    assert(rt_sdl2_set_window_bordered(window, 0) == 1);
    assert(rt_sdl2_set_window_always_on_top(window, 1) == 1);
    assert(rt_sdl2_set_window_fullscreen_checked(0, 1) == 0);
    assert(rt_sdl2_focus_window(0) == 0);
    assert(rt_sdl2_minimize_window(window) == 1);
    assert(rt_sdl2_maximize_window(window) == 1);
    assert(rt_sdl2_restore_window(window) == 1);
    while (rt_sdl2_poll_event() != 0) {}

    SDL_zero(event);
    event.type = SDL_USEREVENT;
    assert(SDL_PushEvent(&event) == 1);
    SDL_zero(event);
    event.type = SDL_TEXTINPUT;
    strcpy(event.text.text, "Simple123");
    assert(SDL_PushEvent(&event) == 1);
    SDL_zero(event);
    event.type = SDL_KEYDOWN;
    event.key.keysym.sym = SDLK_a;
    event.key.keysym.scancode = SDL_SCANCODE_A;
    event.key.keysym.mod = KMOD_CTRL;
    assert(SDL_PushEvent(&event) == 1);

    assert(rt_sdl2_poll_event() == 9);
    assert(strcmp(rt_sdl2_event_text(), "Simple123") == 0);
    assert(rt_sdl2_poll_event() == 2);
    assert(rt_sdl2_event_key_sym() == SDLK_a);
    assert((rt_sdl2_event_key_mod() & KMOD_CTRL) != 0);
    assert(rt_sdl2_poll_event() == 0);
    assert(rt_sdl2_wait_event(1) == 0);

    rt_sdl2_destroy_window(window);
    rt_sdl2_quit();
    return 0;
}
