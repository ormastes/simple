#ifndef SIMPLEOS_CTYPE_H
#define SIMPLEOS_CTYPE_H

static inline int isdigit(int c) { return c >= '0' && c <= '9'; }
static inline int isalpha(int c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}
static inline int isalnum(int c) { return isalpha(c) || isdigit(c); }
static inline int isspace(int c) {
    return c == ' ' || c == '\f' || c == '\n' || c == '\r' || c == '\t' || c == '\v';
}
static inline int isascii(int c) { return (unsigned int)c <= 0x7F; }
static inline int isblank(int c) { return c == ' ' || c == '\t'; }
static inline int iscntrl(int c) { return (unsigned int)c < 0x20 || c == 0x7F; }
static inline int isprint(int c) { return (unsigned int)(c - 0x20) < 0x5F; }
static inline int isgraph(int c) { return (unsigned int)(c - 0x21) < 0x5E; }
static inline int islower(int c) { return c >= 'a' && c <= 'z'; }
static inline int ispunct(int c) { return isgraph(c) && !isalnum(c); }
static inline int isupper(int c) { return c >= 'A' && c <= 'Z'; }
static inline int isxdigit(int c) {
    return isdigit(c) || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f');
}
static inline int tolower(int c) { return isupper(c) ? c + ('a' - 'A') : c; }
static inline int toupper(int c) { return islower(c) ? c - ('a' - 'A') : c; }

typedef struct __simpleos_locale *locale_t;
static inline int isblank_l(int c, locale_t l) { (void)l; return isblank(c); }
static inline int iscntrl_l(int c, locale_t l) { (void)l; return iscntrl(c); }
static inline int isprint_l(int c, locale_t l) { (void)l; return isprint(c); }
static inline int isgraph_l(int c, locale_t l) { (void)l; return isgraph(c); }
static inline int islower_l(int c, locale_t l) { (void)l; return islower(c); }
static inline int ispunct_l(int c, locale_t l) { (void)l; return ispunct(c); }
static inline int isupper_l(int c, locale_t l) { (void)l; return isupper(c); }
static inline int isdigit_l(int c, locale_t l) { (void)l; return isdigit(c); }
static inline int isxdigit_l(int c, locale_t l) { (void)l; return isxdigit(c); }
static inline int tolower_l(int c, locale_t l) { (void)l; return tolower(c); }
static inline int toupper_l(int c, locale_t l) { (void)l; return toupper(c); }

#endif
