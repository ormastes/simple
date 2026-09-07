/* A09 reference fixture — Nuklear widget core, headless.
 *
 * Category: widget-core-headless.
 *   Runs the Nuklear immediate-mode widget core over a fixed 100-frame input
 *   script.  There is NO window, NO renderer, NO font baking, NO rasterization:
 *   Nuklear emits a draw-command list and this fixture counts it.  See
 *   doc/07_guide/ui/ui_slim_gui_references.md for what that number does and does
 *   not mean.
 *
 * Reference only.  Nothing here is part of the Simple product.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define NK_INCLUDE_FIXED_TYPES
#define NK_INCLUDE_STANDARD_IO
#define NK_INCLUDE_STANDARD_VARARGS
#define NK_INCLUDE_DEFAULT_ALLOCATOR
#define NK_IMPLEMENTATION
#include "nuklear.h"

/* EXPECTED_GREETING is what the run ASSERTS is in the draw-command stream and is
 * never affected by the sabotage switch.  GREETING is what the fixture actually
 * renders.  Keeping them separate is what makes --selftest meaningful: a
 * sabotage build that redefined both would still agree with itself. */
#define EXPECTED_GREETING "Hello from Simple UI!"
#ifdef SABOTAGE_NO_GREETING
#define GREETING "..."
#else
#define GREETING EXPECTED_GREETING
#endif

#define BUTTON_LABEL "Click me"
#define FRAMES 100
/* Nuklear reports a button press on the frame the button is RELEASED over its
 * bounds, so the script needs a down frame followed by an up frame with the
 * pointer held on the same widget. */
#define CLICK_DOWN_FRAME 50
#define CLICK_UP_FRAME 51

/* Fixed-metric font: no font baking, no glyph atlas, no freetype.  Text
 * measurement is a pure function of the string length, which keeps the frame
 * deterministic and keeps font-rasterization cost out of the number. */
static float ref_text_width(nk_handle handle, float h, const char *text, int len) {
  (void)handle; (void)h;
  return (float)(8 * len);
}

int main(void) {
  struct nk_context ctx;
  struct nk_user_font font;
  struct timespec t0, t1;
  const struct nk_command *cmd;
  struct nk_rect button_bounds = nk_rect(0, 0, 0, 0);
  int have_bounds = 0;
  int greeting_frames = 0, click_count = 0, total_commands = 0;
  int frame;
  double elapsed_ms;

  memset(&font, 0, sizeof(font));
  font.userdata = nk_handle_ptr(NULL);
  font.height = 16.0f;
  font.width = ref_text_width;

  if (!nk_init_default(&ctx, &font)) {
    fprintf(stderr, "nk_init_default failed\n");
    return 1;
  }

  clock_gettime(CLOCK_MONOTONIC, &t0);

  for (frame = 0; frame < FRAMES; frame++) {
    int commands = 0, greeting_seen = 0;
    int px = 0, py = 0;

    /* --- scripted input for this frame --------------------------------- */
    if (have_bounds) {
      int cx = (int)(button_bounds.x + button_bounds.w / 2.0f);
      int cy = (int)(button_bounds.y + button_bounds.h / 2.0f);
      /* Drift the pointer in, then hold it on the button centre. */
      if (frame < 10) { px = cx * frame / 10; py = cy * frame / 10; }
      else { px = cx; py = cy; }
    }
    nk_input_begin(&ctx);
    nk_input_motion(&ctx, px, py);
    if (frame == CLICK_DOWN_FRAME) { nk_input_button(&ctx, NK_BUTTON_LEFT, px, py, nk_true); }
    if (frame == CLICK_UP_FRAME) { nk_input_button(&ctx, NK_BUTTON_LEFT, px, py, nk_false); }
    nk_input_end(&ctx);

    /* --- widget core ---------------------------------------------------- */
    if (nk_begin(&ctx, "Simple UI Reference", nk_rect(10, 10, 320, 160),
                 NK_WINDOW_BORDER | NK_WINDOW_TITLE | NK_WINDOW_NO_SCROLLBAR)) {
      nk_layout_row_dynamic(&ctx, 24, 1);
      nk_label(&ctx, GREETING, NK_TEXT_LEFT);
      nk_layout_row_dynamic(&ctx, 28, 1);
      /* nk_widget_bounds reports the NEXT widget's screen rect without
       * consuming the layout slot, so the pointer target is discovered from
       * Nuklear itself rather than hardcoded. */
      button_bounds = nk_widget_bounds(&ctx);
      have_bounds = 1;
      if (nk_button_label(&ctx, BUTTON_LABEL)) { click_count++; }
    }
    nk_end(&ctx);

    /* --- draw-command stream -------------------------------------------- */
    nk_foreach(cmd, &ctx) {
      commands++;
      if (cmd->type == NK_COMMAND_TEXT) {
        /* NK_COMMAND_TEXT.string is NOT NUL-terminated: compare with length. */
        const struct nk_command_text *t = (const struct nk_command_text *)cmd;
        if (t->length == (int)strlen(EXPECTED_GREETING) &&
            memcmp(t->string, EXPECTED_GREETING, (size_t)t->length) == 0) {
          greeting_seen = 1;
        }
      }
    }
    nk_clear(&ctx);

    if (greeting_seen) { greeting_frames++; }
    total_commands += commands;
    printf("frame %d commands=%d greeting=%d\n", frame, commands, greeting_seen);
  }

  clock_gettime(CLOCK_MONOTONIC, &t1);
  elapsed_ms = (double)(t1.tv_sec - t0.tv_sec) * 1000.0
             + (double)(t1.tv_nsec - t0.tv_nsec) / 1.0e6;

  nk_free(&ctx);

  printf("category=widget-core-headless\n");
  printf("library=nuklear\n");
  printf("frames=%d\n", FRAMES);
  printf("total_commands=%d\n", total_commands);
  printf("greeting_frames=%d\n", greeting_frames);
  printf("submit_count=%d\n", click_count);
  printf("wall_ms=%.4f\n", elapsed_ms);
  return 0;
}
