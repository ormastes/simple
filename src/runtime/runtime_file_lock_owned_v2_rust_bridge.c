/* Rust runtime compiles this private provider instead of runtime_native.c. */
#define rt_file_lock_owned_acquire_v2 spl_c_file_lock_owned_acquire_v2
#define rt_file_lock_owned_state_v2 spl_c_file_lock_owned_state_v2
#define rt_file_lock_owned_release_v2 spl_c_file_lock_owned_release_v2
#include "runtime_file_lock_owned_v2.h"
