#include <stdint.h>
#include <stdio.h>

extern int64_t dict_len_sequence(void);
extern int64_t dict_len_field(void);
extern int64_t dict_len_alias_field(void);
extern int64_t dict_len_alias_local(void);
extern int64_t dict_len_parameter_case(void);
extern int64_t dict_len_receiver_once(void);
extern int64_t dict_len_nominal(void);
extern int64_t dict_len_nominal_length(void);

int main(void) {
    const int64_t actual[] = {
        dict_len_sequence(), dict_len_field(), dict_len_alias_field(),
        dict_len_alias_local(), dict_len_parameter_case(),
        dict_len_receiver_once(), dict_len_nominal(), dict_len_nominal_length()
    };
    const int64_t expected[] = {0, 2, 1, 3, 2, 1, 23, 28};
    for (unsigned i = 0; i < sizeof(actual) / sizeof(actual[0]); ++i) {
        if (actual[i] != expected[i]) {
            fprintf(stderr, "Dict length case %u: actual=%lld expected=%lld\n",
                    i + 1, (long long)actual[i], (long long)expected[i]);
            return (int)i + 1;
        }
    }
    puts("typed Dict LEN Core C PASS");
    return 0;
}
