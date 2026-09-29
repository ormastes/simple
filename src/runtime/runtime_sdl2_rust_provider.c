/* The pure-C inventory may discover this TU: it stays empty there. Only the
 * Rust runtime owns the public text/array ABI wrappers below. */
#if defined(SIMPLE_RUNTIME_RUST_SDL_PROVIDER)
#define rt_sdl2_create_window spl_sdl2_create_window_cstr
#define rt_sdl_create_window spl_sdl_create_window_cstr
#define rt_sdl2_set_window_title spl_sdl2_set_window_title_cstr
#define rt_sdl_set_window_title spl_sdl_set_window_title_cstr
#define rt_sdl2_event_text spl_sdl2_event_text_cstr
#define rt_sdl_event_text spl_sdl_event_text_cstr
#define rt_sdl2_last_error spl_sdl2_last_error_cstr
#define rt_sdl2_clipboard_get spl_sdl2_clipboard_get_cstr
#define rt_sdl2_clipboard_set spl_sdl2_clipboard_set_cstr
#define rt_sdl2_get_display_name spl_sdl2_get_display_name_cstr
#define rt_sdl2_present_rgba spl_sdl2_present_rgba_core_array
#define rt_sdl_present_rgba spl_sdl_present_rgba_core_array
#include "runtime_sdl2.c"
#endif
