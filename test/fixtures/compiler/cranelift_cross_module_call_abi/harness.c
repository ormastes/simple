/* C harness for the two-module Cranelift call ABI fixture: calls the
 * caller module's entry and prints its value. Built with -DCV_CASE_<case>. */
#include <stdio.h>
#include <stdint.h>
#if defined(CV_CASE_untyped)
extern int64_t cv_go_untyped(void) __asm__("cv_cross_module_call_abi.cv_go_untyped");
int main(void) { printf("cv=%lld\n", (long long)cv_go_untyped()); return 0; }
#elif defined(CV_CASE_i64)
extern int64_t cv_go_i64(void) __asm__("cv_cross_module_call_abi.cv_go_i64");
int main(void) { printf("cv=%lld\n", (long long)cv_go_i64()); return 0; }
#elif defined(CV_CASE_int_to_f64)
extern double cv_go_int_to_f64(void) __asm__("cv_cross_module_call_abi.cv_go_int_to_f64");
int main(void) { printf("cv=%.3f\n", cv_go_int_to_f64()); return 0; }
#elif defined(CV_CASE_match)
extern double cv_go_match(void) __asm__("cv_cross_module_call_abi.cv_go_match");
int main(void) { printf("cv=%.3f\n", cv_go_match()); return 0; }
#elif defined(CV_CASE_match_i64)
extern int64_t cv_go_match_i64(void) __asm__("cv_cross_module_call_abi.cv_go_match_i64");
int main(void) { printf("cv=%lld\n", (long long)cv_go_match_i64()); return 0; }
#endif
