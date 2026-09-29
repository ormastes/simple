#include <stdint.h>
#include <stdio.h>

int64_t rt_range(int64_t start, int64_t end);
int64_t rt_array_len(void *array);
int64_t rt_array_get(void *array, int64_t index);
int64_t rt_value_as_int(int64_t value);

static int check_range(int64_t start, int64_t end, const int64_t *want, int64_t count) {
    int64_t value = rt_range(start, end);
    void *array = (void *)(uintptr_t)value;
    if (rt_array_len(array) != count) return 0;
    for (int64_t i = 0; i < count; i++) {
        if (rt_value_as_int(rt_array_get(array, i)) != want[i]) return 0;
    }
    return 1;
}

int main(void) {
    const int64_t positive[] = {2, 3, 4};
    const int64_t negative[] = {-2, -1, 0, 1};
    if (!check_range(2, 5, positive, 3)) return 1;
    if (!check_range(-2, 2, negative, 4)) return 2;
    if (!check_range(7, 7, positive, 0)) return 3;
    if (!check_range(9, 3, positive, 0)) return 4;
    puts("PASS runtime range ABI");
    return 0;
}
