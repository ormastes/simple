#ifndef SIMPLEOS_WCTYPE_H
#define SIMPLEOS_WCTYPE_H

#include <wchar.h>

static inline int iswspace(wint_t c) { return c == ' ' || (c >= '\t' && c <= '\r'); }
static inline int iswprint(wint_t c) { return c >= 0x20 && c < 0x7f; }
static inline int iswcntrl(wint_t c) { return c < 0x20 || c == 0x7f; }
static inline int iswupper(wint_t c) { return c >= 'A' && c <= 'Z'; }
static inline int iswlower(wint_t c) { return c >= 'a' && c <= 'z'; }
static inline int iswalpha(wint_t c) { return iswupper(c) || iswlower(c); }
static inline int iswblank(wint_t c) { return c == ' ' || c == '\t'; }
static inline int iswdigit(wint_t c) { return c >= '0' && c <= '9'; }
static inline int iswpunct(wint_t c) { return iswprint(c) && !iswalpha(c) && !iswdigit(c) && !iswblank(c); }
static inline int iswxdigit(wint_t c) {
    return iswdigit(c) || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f');
}
static inline wint_t towupper(wint_t c) { return iswlower(c) ? c - ('a' - 'A') : c; }
static inline wint_t towlower(wint_t c) { return iswupper(c) ? c + ('a' - 'A') : c; }

typedef struct __simpleos_locale *locale_t;
static inline int iswspace_l(wint_t c, locale_t l) { (void)l; return iswspace(c); }
static inline int iswprint_l(wint_t c, locale_t l) { (void)l; return iswprint(c); }
static inline int iswcntrl_l(wint_t c, locale_t l) { (void)l; return iswcntrl(c); }
static inline int iswupper_l(wint_t c, locale_t l) { (void)l; return iswupper(c); }
static inline int iswlower_l(wint_t c, locale_t l) { (void)l; return iswlower(c); }
static inline int iswalpha_l(wint_t c, locale_t l) { (void)l; return iswalpha(c); }
static inline int iswblank_l(wint_t c, locale_t l) { (void)l; return iswblank(c); }
static inline int iswdigit_l(wint_t c, locale_t l) { (void)l; return iswdigit(c); }
static inline int iswpunct_l(wint_t c, locale_t l) { (void)l; return iswpunct(c); }
static inline int iswxdigit_l(wint_t c, locale_t l) { (void)l; return iswxdigit(c); }
static inline wint_t towupper_l(wint_t c, locale_t l) { (void)l; return towupper(c); }
static inline wint_t towlower_l(wint_t c, locale_t l) { (void)l; return towlower(c); }

#endif
