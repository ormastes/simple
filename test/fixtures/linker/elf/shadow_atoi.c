/* Overrides libc's atoi. Used to prove DT_NEEDED ORDER, not just the set:
   whichever library comes first in DT_NEEDED wins at resolution time. */
int atoi(const char *s) { (void) s; return 42; }
