/* A09 reference fixture — microui widget core, headless.
 *
 * Category: widget-core-headless.
 *   Runs the microui immediate-mode widget core over a fixed 100-frame input
 *   script.  There is NO window, NO renderer, NO rasterization: microui emits a
 *   draw-command list and this fixture counts it.  See
 *   doc/07_guide/ui/ui_slim_gui_references.md for what that number does and does
 *   not mean.
 *
 * Reference only.  Nothing here is part of the Simple product.
 */
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "microui.h"

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
/* The click is scripted at a fixed frame so the run is byte-deterministic.
 * hover must be established on a frame where the button is NOT held down
 * (mu_update_control only sets hover when !mouse_down), so the press frame is
 * preceded by pure pointer motion. */
#define CLICK_DOWN_FRAME 50
#define CLICK_UP_FRAME 51

static int text_width(mu_Font font, const char *str, int len) {
  (void)font;
  if (len < 0) { len = (int)strlen(str); }
  return 8 * len;
}

static int text_height(mu_Font font) { (void)font; return 16; }

/* The button is placed at an EXPLICIT absolute rect via mu_layout_set_next, so
 * the scripted pointer target is the rect the widget actually occupies rather
 * than a guess at what the default layout produced.  Reading the rect back out
 * of the command list is not an option: microui reorders root-container
 * commands with jump commands, so command-list order is not emission order. */
#define BUTTON_X 20
#define BUTTON_Y 96
#define BUTTON_W 140
#define BUTTON_H 28

typedef struct {
  int commands;      /* total draw commands emitted this frame */
  int greeting_seen; /* greeting text command present this frame */
} FrameStats;

static void scan_frame(mu_Context *ctx, FrameStats *st) {
  mu_Command *cmd = NULL;
  st->commands = 0;
  st->greeting_seen = 0;
  while (mu_next_command(ctx, &cmd)) {
    st->commands++;
    if (cmd->type == MU_COMMAND_TEXT && strcmp(cmd->text.str, EXPECTED_GREETING) == 0) {
      st->greeting_seen = 1;
    }
  }
}

int main(void) {
  static mu_Context ctx;
  struct timespec t0, t1;
  FrameStats st;
  const int cx = BUTTON_X + BUTTON_W / 2;
  const int cy = BUTTON_Y + BUTTON_H / 2;
  int greeting_frames = 0, submit_count = 0, total_commands = 0;
  int frame, px = 0, py = 0;
  double elapsed_ms;

  mu_init(&ctx);
  ctx.text_width = text_width;
  ctx.text_height = text_height;

  clock_gettime(CLOCK_MONOTONIC, &t0);

  for (frame = 0; frame < FRAMES; frame++) {
    int res;

    /* --- scripted input for this frame --------------------------------- */
    /* Drift the pointer in over the first frames so the script exercises real
     * pointer motion, then hold it on the button centre. */
    if (frame < 10) {
      px = cx * frame / 10;
      py = cy * frame / 10;
    } else {
      px = cx;
      py = cy;
    }
    mu_input_mousemove(&ctx, px, py);
    if (frame == CLICK_DOWN_FRAME) { mu_input_mousedown(&ctx, px, py, MU_MOUSE_LEFT); }
    if (frame == CLICK_UP_FRAME) { mu_input_mouseup(&ctx, px, py, MU_MOUSE_LEFT); }

    /* --- widget core ---------------------------------------------------- */
    mu_begin(&ctx);
    if (mu_begin_window(&ctx, "Simple UI Reference", mu_rect(10, 10, 320, 140))) {
      int widths[1] = { -1 };
      mu_layout_row(&ctx, 1, widths, 24);
      mu_label(&ctx, GREETING);
      mu_layout_set_next(&ctx, mu_rect(BUTTON_X, BUTTON_Y, BUTTON_W, BUTTON_H), 0);
      res = mu_button(&ctx, BUTTON_LABEL);
      if (res & MU_RES_SUBMIT) { submit_count++; }
      mu_end_window(&ctx);
    }
    mu_end(&ctx);

    scan_frame(&ctx, &st);
    if (st.greeting_seen) { greeting_frames++; }
    total_commands += st.commands;
    printf("frame %d commands=%d greeting=%d\n", frame, st.commands, st.greeting_seen);
  }

  clock_gettime(CLOCK_MONOTONIC, &t1);
  elapsed_ms = (double)(t1.tv_sec - t0.tv_sec) * 1000.0
             + (double)(t1.tv_nsec - t0.tv_nsec) / 1.0e6;

  printf("category=widget-core-headless\n");
  printf("library=microui\n");
  printf("frames=%d\n", FRAMES);
  printf("total_commands=%d\n", total_commands);
  printf("greeting_frames=%d\n", greeting_frames);
  printf("submit_count=%d\n", submit_count);
  printf("wall_ms=%.4f\n", elapsed_ms);
  return 0;
}
