/* String-merge fixture B (lane C1): duplicates of A's "hi\n" and "dup\n",
   plus its own "only-b\n". merge_b returns 40 regardless of its argument. */
const char *b_hi(void) { return "hi\n"; }
const char *b_dup(void) { return "dup\n"; }
const char *b_only(void) { return "only-b\n"; }

long merge_b(const char *s) { return (s == 0) ? 0 : 40; }
