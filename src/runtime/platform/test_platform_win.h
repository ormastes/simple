/*
 * Windows-specific test cases — stubs for now.
 *
 * Included by runtime_test.c via test_platform.h.
 * Requires TEST/RUN/ASSERT macros to be defined before inclusion.
 */
#ifndef SPL_TEST_PLATFORM_WIN_H
#define SPL_TEST_PLATFORM_WIN_H

TEST(dir_create_recursive_windows) {
    const char* root = ".\\rt_test_win_mkdir";
    const char* leaf = ".\\rt_test_win_mkdir\\a\\b\\c";
    if (spl_file_exists(root)) {
        rt_dir_remove_all(root);
    }
    ASSERT(rt_dir_create(leaf, true));
    ASSERT(spl_file_exists(".\\rt_test_win_mkdir\\a"));
    ASSERT(spl_file_exists(leaf));
    ASSERT(rt_dir_remove_all(root));
}

static void run_platform_tests(void) {
    printf("\n--- Platform Tests (Windows) ---\n");
    RUN(dir_create_recursive_windows);

    run_cpu_tests();
}

#endif /* SPL_TEST_PLATFORM_WIN_H */
