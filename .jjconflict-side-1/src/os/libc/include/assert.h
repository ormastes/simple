/*
 * SimpleOS <assert.h> — runtime assertions
 *
 * Note: This header is intentionally missing an include guard so that
 * re-inclusion after redefining NDEBUG changes the assert behavior.
 */

#undef assert

#ifdef __cplusplus
extern "C" {
#endif

void __assert_fail(const char *expr, const char *file,
                   unsigned int line, const char *func)
    __attribute__((noreturn));

#ifdef __cplusplus
}
#endif

#ifdef NDEBUG
#define assert(expr) ((void)0)
#else
#define assert(expr) \
    ((expr) ? ((void)0) : \
     __assert_fail(#expr, __FILE__, __LINE__, __func__))
#endif
