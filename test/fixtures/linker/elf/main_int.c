/* Exits with atoi(s): 42 when a shadowing library is searched before libc,
   1 when libc is. Nothing but the DT_NEEDED ORDER distinguishes the two
   links -- the SET is identical either way. `s` is a global and builtins are
   off so the call cannot be constant-folded away. */
extern int atoi(const char *);
const char *s = "1";
int main(void) { return atoi(s); }
