#include <assert.h>
#include <stdlib.h>
#include <string.h>

RuntimeValue *runtime_array_items(RuntimeArray *array)
{
    return array->items;
}

RuntimeValue rt_value_to_string(RuntimeValue value)
{
    return value;
}

RuntimeValue rt_string_from_cstr(const char *text)
{
    size_t len = strlen(text);
    RuntimeString *out = malloc(sizeof(*out) + len + 1);
    assert(out != NULL);
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(*out) + len + 1);
    out->len = (uint32_t)len;
    memcpy(out->data, text, len + 1);
    return ENCODE_PTR(out);
}

RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len)
{
    const char *source = (const char *)(uintptr_t)data;
    RuntimeString *out = malloc(sizeof(*out) + (size_t)len + 1);
    assert(out != NULL);
    out->hdr.type = HEAP_STRING;
    out->len = (uint32_t)len;
    memcpy(out->data, source, (size_t)len);
    out->data[len] = '\0';
    return ENCODE_PTR(out);
}

RuntimeValue rt_string_concat(RuntimeValue left, RuntimeValue right)
{
    RuntimeString *a = DECODE_PTR(left);
    RuntimeString *b = DECODE_PTR(right);
    size_t len = a->len + b->len;
    RuntimeString *out = malloc(sizeof(*out) + len + 1);
    assert(out != NULL);
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(*out) + len + 1);
    out->len = (uint32_t)len;
    memcpy(out->data, a->data, a->len);
    memcpy(out->data + a->len, b->data, b->len + 1);
    return ENCODE_PTR(out);
}

RuntimeString *decode_string(RuntimeValue value)
{
    return (RuntimeString *)DECODE_PTR(value);
}

RuntimeValue rt_array_new(RuntimeValue capacity)
{
    uint32_t cap = (uint32_t)(capacity >> 3);
    RuntimeArray *array = calloc(1, sizeof(*array));
    assert(array != NULL);
    array->hdr.type = HEAP_ARRAY;
    array->cap = cap;
    array->items = cap ? calloc(cap, sizeof(*array->items)) : NULL;
    return ENCODE_PTR(array);
}

static RuntimeValue rt_array_push_handle(RuntimeValue value, RuntimeValue item)
{
    RuntimeArray *array = DECODE_PTR(value);
    array->items = realloc(array->items, (array->len + 1) * sizeof(*array->items));
    assert(array->items != NULL);
    array->items[array->len++] = item;
    return value;
}

RuntimeValue rt_string_slice(RuntimeValue value, RuntimeValue start, RuntimeValue end)
{
    RuntimeString *source = DECODE_PTR(value);
    assert(start >= 0 && end >= start && (uint32_t)end <= source->len);
    RuntimeString *out = malloc(sizeof(*out) + (size_t)(end - start) + 1);
    assert(out != NULL);
    out->hdr.type = HEAP_STRING;
    out->len = (uint32_t)(end - start);
    memcpy(out->data, source->data + start, out->len);
    out->data[out->len] = '\0';
    return ENCODE_PTR(out);
}

static RuntimeValue text_array(RuntimeValue *items, uint32_t len)
{
    RuntimeArray *array = calloc(1, sizeof(*array));
    assert(array != NULL);
    array->hdr.type = HEAP_ARRAY;
    array->len = len;
    array->cap = len;
    array->items = items;
    return ENCODE_PTR(array);
}

static void expect_text(RuntimeValue value, const char *expected)
{
    RuntimeString *text = DECODE_PTR(value);
    assert(text != NULL);
    assert(text->len == strlen(expected));
    assert(memcmp(text->data, expected, text->len + 1) == 0);
}

int main(void)
{
    RuntimeValue items[] = {
        rt_string_from_cstr("DB"),
        rt_string_from_cstr("FS"),
        rt_string_from_cstr("NS3"),
    };
    RuntimeValue array = text_array(items, 3);
    RuntimeValue empty_separator = rt_string_from_cstr("");
    RuntimeValue pipe_separator = rt_string_from_cstr("|");
    RuntimeValue empty = text_array(NULL, 0);

    /* The DBFS decoder uses exactly this join path for header and body text. */
    expect_text(rt_string_join(array, empty_separator), "DBFSNS3");
    expect_text(rt_string_join(array, pipe_separator), "DB|FS|NS3");
    expect_text(rt_string_join(empty, empty_separator), "");

    /* DBFSNS3's generation and Adler checksum are decimal header fields. */
    assert(rt_string_to_int(rt_string_from_cstr("1")) == 1);
    assert(rt_string_to_int(rt_string_from_cstr("3319668373")) == 3319668373LL);
    assert(rt_string_to_int(rt_string_from_cstr("  +42rest")) == 42);
    assert(rt_string_to_int(rt_string_from_cstr("-17")) == -17);
    assert(rt_string_to_int(rt_string_from_cstr("not-a-number")) == 0);
    assert(rt_string_to_int(rt_string_from_cstr("999999999999999999999")) == INT64_MAX);
    assert(rt_string_to_int(rt_string_from_cstr("-999999999999999999999")) == INT64_MIN);

    RuntimeValue parts = rt_string_split(
        rt_string_from_cstr("DBFSNS3|1|3319668373"), pipe_separator);
    RuntimeArray *fields = DECODE_PTR(parts);
    assert(fields->len == 3);
    expect_text(fields->items[0], "DBFSNS3");
    expect_text(fields->items[1], "1");
    expect_text(fields->items[2], "3319668373");

    RuntimeValue lines = rt_string_split(
        rt_string_from_cstr("DBFSNS3|1|3319668373\nF|2"),
        rt_string_from_cstr("\n"));
    RuntimeArray *rows = DECODE_PTR(lines);
    assert(rows->len == 2);
    expect_text(rows->items[0], "DBFSNS3|1|3319668373");
    expect_text(rows->items[1], "F|2");

    /* The decoder builds every checkpoint byte through this raw-codepoint ABI. */
    expect_text(rt_char_from_code(68), "D");
    expect_text(rt_char_from_code(70), "F");
    expect_text(rt_char_from_code(124), "|");
    expect_text(rt_char_from_code(52), "4");
    return 0;
}
