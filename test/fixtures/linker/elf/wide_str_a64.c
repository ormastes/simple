/* .rodata.str4.4 (UTF-32 wchar_t) merge-string input for the internal linker. */
#include <wchar.h>
int main(void) {
    const wchar_t *a = L"wide";
    const wchar_t *b = L"wide";
    return (int)(wcslen(a) + wcslen(b)) + 36;
}
