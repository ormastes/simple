# Native exit zero without the completion receipt must fail

```simple
extern fn rt_exit(code: i64)
rt_exit(0)
```
