/* DIFFERENT bytes from libshadowatoi_a64.so, but the SAME DT_SONAME.
   ld de-duplicates shared inputs by SONAME, so it records one DT_NEEDED;
   a content-digest dedup sees two distinct files and records two. */
int atoi(const char *s) { (void) s; return 99; }
