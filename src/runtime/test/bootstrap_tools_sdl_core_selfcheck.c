/* Exercise both the established C array adapter and the new raw pixel view
 * on real SDL software surfaces, comparing their rendered pixel bytes. */
#include "../runtime_sdl2.c"
#include <stdio.h>
#include <string.h>

#define REQUIRE(check) do { if (!(check)) { fprintf(stderr, "SDL core check failed at line %d: %s\n", __LINE__, #check); return 1; } } while (0)

int main(void) {
    REQUIRE(rt_sdl2_init() == 1);
    int64_t legacy_window = rt_sdl2_create_window("legacy", 2, 1);
    int64_t view_window = rt_sdl2_create_window("view", 2, 1);
    REQUIRE(legacy_window && view_window);
    int64_t raw[] = {0x123456ff, 0xfedcba80};
    SplValue items[] = {spl_int(raw[0]), spl_int(raw[1])};
    SplArray array = {items, 2, 2};
    REQUIRE(rt_sdl2_present_rgba(legacy_window, &array, 2, 1));
    REQUIRE(spl_sdl2_present_rgba_i64_view(view_window, raw, 2, 2, 1));
    SDL_Surface* legacy = SDL_GetWindowSurface(sdl2_window_get(legacy_window));
    SDL_Surface* view = SDL_GetWindowSurface(sdl2_window_get(view_window));
    REQUIRE(legacy && view && legacy->pixels && view->pixels);
    REQUIRE(legacy->w == 2 && view->w == 2);
    REQUIRE(memcmp(legacy->pixels, view->pixels, 8) == 0);
    REQUIRE(memcmp(view->pixels, (const uint8_t*)view->pixels + 4, 4) != 0);
    REQUIRE(!spl_sdl2_present_rgba_i64_view(view_window, raw, 1, 2, 1));
    REQUIRE(!spl_sdl2_present_rgba_i64_view(view_window, NULL, 2, 2, 1));
    REQUIRE(!rt_sdl2_present_rgba(legacy_window, &array, 3, 1));
    rt_sdl2_destroy_window(legacy_window);
    rt_sdl2_destroy_window(view_window);
    REQUIRE(rt_sdl2_quit());
    puts("SDL core/raw pixel view parity PASS");
    return 0;
}
