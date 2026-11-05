#include <assert.h>
#include <stdlib.h>
#include <string.h>

static RuntimeValue heap_text(const char *text)
{
    size_t len = strlen(text);
    RuntimeString *value = malloc(sizeof(*value) + len + 1);
    assert(value != NULL);
    value->hdr.type = HEAP_STRING;
    value->hdr.size = (uint32_t)(sizeof(*value) + len + 1);
    value->len = len;
    memcpy(value->data, text, len + 1);
    return ENCODE_PTR(value);
}

int main(void)
{
    RuntimeValue ready_a = heap_text("ready");
    RuntimeValue ready_b = heap_text("ready");
    RuntimeValue fatal = heap_text("nvme-controller-fatal");
    char raw_ready_a[] = "ready";
    char raw_ready_b[] = "ready";
    char raw_fatal[] = "nvme-controller-fatal";

    /* The exact NVMe admission comparisons, with independent allocations. */
    assert(rt_text_eq_any(ready_a, ready_b) == 1);
    assert(rt_text_eq_any(ready_a, fatal) == 0);
    assert(rt_text_eq_any(ready_a, (RuntimeValue)(uintptr_t)raw_ready_a) == 1);
    assert(rt_text_eq_any((RuntimeValue)(uintptr_t)raw_ready_a, ready_a) == 1);
    assert(rt_text_eq_any(ready_a, (RuntimeValue)(uintptr_t)raw_fatal) == 0);

    assert(rt_text_eq_any((RuntimeValue)(uintptr_t)raw_ready_a,
                          (RuntimeValue)(uintptr_t)raw_ready_b) == 1);
    assert(rt_text_eq_any((RuntimeValue)(uintptr_t)raw_ready_a,
                          (RuntimeValue)(uintptr_t)raw_fatal) == 0);
    assert(rt_text_eq_any(NIL_VALUE, NIL_VALUE) == 1);
    assert(rt_text_eq_any(NIL_VALUE, ready_a) == 0);
    assert(rt_text_eq_any(0, ready_a) == 0);
    assert(rt_text_eq_any(ENCODE_INT(1), ENCODE_INT(2)) == 0);

    free(DECODE_PTR(ready_a));
    free(DECODE_PTR(ready_b));
    free(DECODE_PTR(fatal));
    return 0;
}
