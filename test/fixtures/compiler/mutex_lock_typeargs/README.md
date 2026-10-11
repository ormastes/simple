# Return-only `mutex_lock<T>` type argument cases

All cases are UNEXECUTED. `main.spl` checks an explicitly typed integer
sentinel lock. `no_result_context.spl` reproduces E-MONO-032 because the
generic result type appears nowhere in the `Mutex` argument and has no result
context. `text_value.spl` ensures the explicit call type remains generic and
is not globally hardcoded to `i64`.

Expected: `main.spl` and `text_value.spl` object/link/run with exit 0;
`no_result_context.spl` rejects at monomorphization with E-MONO-032 and emits
no object. These expectations are authored, not executed evidence.
