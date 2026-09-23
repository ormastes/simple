#include "runtime.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Intentionally link-fails on #1417: presentation alone has no event lifecycle. */
extern void rt_gui_begin_session(void);
extern void rt_gui_session_present_html(int64_t html);
extern int64_t rt_gui_poll_event(void);
extern void rt_gui_end_session(void);

int main(void) {
    rt_gui_begin_session();
    rt_gui_session_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    int64_t event = rt_gui_poll_event();
    assert(rt_string_len(event) == 12);
    assert(memcmp(rt_string_data(event), "text\nhello\nx", 12) == 0);
    rt_gui_end_session();
    puts("GUI event lifecycle PASS");
    return 0;
}
