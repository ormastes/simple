/* Link /SUBSYSTEM:WINDOWS and launch with no console (CREATE_NO_WINDOW).
 * A genuine CRT -2 descriptor is required; no forged FILE or monkeypatch. */
#include <windows.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <wchar.h>
extern int64_t rt_string_new(const uint8_t *, uint64_t);
extern int64_t rt_term_write(int64_t);
static unsigned invalid_calls;
static void invalid_parameter(const wchar_t *expression,const wchar_t *function,
 const wchar_t *file,unsigned line,uintptr_t reserved) {
 (void)expression;(void)function;(void)file;(void)line;(void)reserved;++invalid_calls;
}
int WINAPI WinMain(HINSTANCE instance,HINSTANCE previous,LPSTR command,int show) {
 (void)instance;(void)previous;(void)command;(void)show;
 _invalid_parameter_handler old=_set_invalid_parameter_handler(invalid_parameter);
 int descriptor=_fileno(stdout);
 if(descriptor!=-2){_set_invalid_parameter_handler(old);return 20;}
 int64_t value=rt_string_new((const uint8_t*)"raw\n",4);
 int64_t written=rt_term_write(value);
 _set_invalid_parameter_handler(old);
 return written==0&&invalid_calls==0?0:21;
}
