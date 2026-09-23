# SimpleOS `cos(0)` one-ULP overshoot

Status: FIXED IN SOURCE; TARGET VERIFICATION DEFERRED

The SimpleOS libc `cos` provider previously evaluated cosine as
`sin(x + pi/2)`. At zero, rounding in the shifted sine Taylor series could
produce the next representable value above `1.0`, violating the exact IEEE
identity and the mathematical range of cosine.

The kernel now folds the reduced argument into `[-pi/2, pi/2]` and uses the
direct even Taylor recurrence. It has the same twelve recurrence steps as
`sin`, allocates no memory, removes the phase-shift addition, and returns
exactly `1.0` for both signed zeros and exactly `-1.0` at the provider's `pi`.

TODO(simpleos-native-qemu): when the admitted phase compiler/runtime is ready,
run the 91-check native parity harness and the focused exact-zero regression on
the native binary and SimpleOS QEMU. Record latency and maximum RSS against the
shifted-sine kernel; reject any throughput or memory regression.
