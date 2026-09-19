/* Wide-literal fixture B (lane C1): the same L"wide" literal as
   merge_wide_a64.c, in its own object. */
typedef __WCHAR_TYPE__ wchar_t;
const wchar_t *wide_b(void) { return L"wide"; }
