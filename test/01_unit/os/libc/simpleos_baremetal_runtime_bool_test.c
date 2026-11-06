/* owner_bool.inc contains the selected owner's real macros, types and bodies.
 * No architecture-specific instructions or unrelated runtime stubs are linked. */
#include <assert.h>
#include "owner_bool.inc"

_Static_assert(TRUE_VALUE == 11, "tagged true is not encoded integer one");
_Static_assert(FALSE_VALUE == 19, "tagged false is not encoded integer zero");

int main(void)
{
#if SIMPLEOS_BOOL_HAS_LOGICAL
    const RuntimeValue values[] = {
        TRUE_VALUE, FALSE_VALUE, ENCODE_INT(0), ENCODE_INT(1),
        ENCODE_INT(-1), ENCODE_INT(2), NIL_VALUE, 0
    };
    const int truthy[] = { 1, 0, 0, 1, 1, 1, 0, 0 };
    const unsigned count = sizeof(values) / sizeof(values[0]);
    for (unsigned i = 0; i < count; ++i) {
        assert(rt_not(values[i]) == (truthy[i] ? FALSE_VALUE : TRUE_VALUE));
        assert(rt_to_bool(values[i]) == (truthy[i] ? TRUE_VALUE : FALSE_VALUE));
        /* This legacy predicate returns raw 0/1; it does not box its result.
         * Integer zero/one are not booleans despite sharing truthiness. */
        assert(rt_is_bool(values[i]) == (i < 2 ? 1 : 0));
        for (unsigned j = 0; j < count; ++j) {
            assert(rt_and(values[i], values[j]) ==
                   (truthy[i] && truthy[j] ? TRUE_VALUE : FALSE_VALUE));
            assert(rt_or(values[i], values[j]) ==
                   (truthy[i] || truthy[j] ? TRUE_VALUE : FALSE_VALUE));
        }
    }
#endif
    return 0;
}
