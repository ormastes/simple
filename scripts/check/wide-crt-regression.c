#include <windows.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <wchar.h>
#include <string.h>
#include "platform/runtime_win_remove_tree.h"
#define CHECK(x) do { if (!(x)) { fprintf(stderr, "failed line %d: %s error=%lu\n", __LINE__, #x, GetLastError()); return 1; } } while (0)
static wchar_t module_path[32769];
static DWORD test_module(HMODULE module, wchar_t *out, DWORD capacity) {
    (void)module;
    size_t length = wcslen(module_path);
    if (length >= capacity) return capacity;
    memcpy(out, module_path, (length + 1) * sizeof(*out));
    return (DWORD)length;
}
#define GetModuleFileNameW test_module
#include "mcp-wide-functions.h"
#undef GetModuleFileNameW
static int file(const wchar_t *path) {
    HANDLE h = CreateFileW(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (h == INVALID_HANDLE_VALUE) return 0;
    return CloseHandle(h) != 0;
}
int main(int argc, char **argv) {
    CHECK(argc == 2);
    wchar_t base[32768], path[32768], expected[32768], wrapper[32768];
    CHECK(MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, argv[1], -1, base, 32768));
    CHECK(swprintf(path, 32768, L"%ls\\tree", base) > 0);
    CHECK(CreateDirectoryW(path, NULL));
    wchar_t *extended = rt_win_long_path_widen(argv[1]); CHECK(extended); free(extended);
    /* Start with a short root and descendants beyond MAX_PATH. */
    CHECK(swprintf(path, 32768, L"\\\\?\\%ls\\tree", base) > 0);
    for (int i = 0; i < 12; ++i) {
        size_t at = wcslen(path);
        CHECK(swprintf(path + at, 32768 - at, L"\\directory_%02d_abcdefghijklmnop", i) > 0);
        CHECK(CreateDirectoryW(path, NULL));
    }
    CHECK(wcslen(path) > MAX_PATH);
    size_t at = wcslen(path); CHECK(swprintf(path + at, 32768 - at, L"\\leaf.txt") > 0); CHECK(file(path));
    char tree[32768]; CHECK(snprintf(tree, sizeof tree, "%s/tree", argv[1]) > 0);
    CHECK(rt_win_remove_tree_utf8(tree, false, false));
    CHECK(rt_win_remove_tree_utf8(tree, true, false));
    CHECK(!rt_win_remove_tree_utf8(tree, false, false));
    CHECK(!rt_win_remove_tree_utf8(NULL, false, false)); CHECK(!rt_win_remove_tree_utf8("", true, true));
    CHECK(!rt_win_remove_tree_utf8("\xff", true, true));
    CHECK(swprintf(path, 32768, L"%ls\\trailing", base) > 0); CHECK(CreateDirectoryW(path, NULL));
    at = wcslen(path); CHECK(swprintf(path + at, 32768 - at, L"\\child.txt") > 0); CHECK(file(path));
    path[at] = L'\\'; path[at + 1] = 0;
    CHECK(rt_win_remove_tree_wide(path, false));
    CHECK(swprintf(path, 32768, L"%ls\\file.txt", base) > 0); CHECK(file(path));
    char leaf[32768]; CHECK(snprintf(leaf, sizeof leaf, "%s/file.txt", argv[1]) > 0);
    CHECK(!rt_win_remove_tree_utf8(leaf, false, false)); CHECK(rt_win_remove_tree_utf8(leaf, false, true));
    CHECK(swprintf(path, 32768, L"%ls\\a", base) > 0); CHECK(CreateDirectoryW(path, NULL));
    CHECK(swprintf(path, 32768, L"%ls\\a\\b", base) > 0); CHECK(CreateDirectoryW(path, NULL));
    CHECK(swprintf(module_path, 32769, L"%ls\\a\\b\\tool.exe", base) > 0);
    CHECK(swprintf(expected, 32768, L"%ls\\simple_mcp_server.cmd", base) > 0); CHECK(file(expected));
    CHECK(rt_mcp_wrapper_w(wrapper, 32768)); CHECK(wcscmp(wrapper, expected) == 0);
    CHECK(!rt_mcp_wrapper_w(wrapper, 1)); CHECK(DeleteFileW(expected));
    CHECK(swprintf(expected, 32768, L"%ls\\a\\b\\simple_mcp_server.cmd", base) > 0); CHECK(file(expected));
    CHECK(rt_mcp_wrapper_w(wrapper, 32768)); CHECK(wcscmp(wrapper, expected) == 0);
    CHECK(SetEnvironmentVariableW(L"_SIMPLE_STACK_SET", L"hidden"));
    CHECK(SetEnvironmentVariableW(L"_SIMPLE_MCP_WRAPPER_PATH", L"old"));
    CHECK(SetEnvironmentVariableW(L"SIMPLE_CRT_RETAIN", L"preserved"));
    wchar_t *environment = rt_mcp_environment_w(wrapper); CHECK(environment);
    int routes = 0, retained = 0;
    for (const wchar_t *entry = environment; *entry; entry += wcslen(entry) + 1) {
        CHECK(_wcsnicmp(entry, L"_SIMPLE_STACK_SET=", 18) != 0);
        if (_wcsnicmp(entry, L"_SIMPLE_MCP_WRAPPER_PATH=", 25) == 0) { ++routes; CHECK(wcscmp(entry + 25, wrapper) == 0); }
        if (wcscmp(entry, L"SIMPLE_CRT_RETAIN=preserved") == 0) ++retained;
    }
    free(environment); CHECK(routes == 1 && retained == 1);
    /* Root-parent fallback restores the complete exe directory including NUL. */
    memcpy(module_path, L"C:\\tool.exe", sizeof L"C:\\tool.exe");
    CHECK(!rt_mcp_wrapper_w(wrapper, 1));
    wmemset(module_path, L'x', 32768); module_path[32768] = 0;
    CHECK(!rt_mcp_wrapper_w(wrapper, 32768));
    module_path[0] = L'C'; module_path[1] = L':'; module_path[2] = L'\\';
    memcpy(module_path + 32758, L"\\tool.exe", sizeof L"\\tool.exe");
    CHECK(wcslen(module_path) == 32767);
    CHECK(!rt_mcp_wrapper_w(wrapper, 1));
    CHECK(swprintf(path, 32768, L"%ls\\a", base) > 0); CHECK(rt_win_remove_tree_wide(path, false));
    puts("PASS wide CRT: long tree, missing/file/trailing boundaries, wrapper paths, environment copy");
    return 0;
}
