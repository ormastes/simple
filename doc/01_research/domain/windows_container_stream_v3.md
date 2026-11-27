# Windows stream native boundary research

Microsoft documents Job CPU hard-cap rates in 1/100 percent units, and nested
job rates relative to rate-controlled ancestors. The initial managed profile
therefore requires an actually observed unnested host and one processor group;
it refuses an unknown parent hierarchy and does not request breakaway.
[CPU rate information](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_cpu_rate_control_information).

With N observed logical processors, a whole-millicore grant requires
`rate = cpu_millis * 10 / N` exactly, within 1..10000. The supported integer
quantum is `N / gcd(N,10)` millicores. No rounding above the grant is admitted.
[Processor groups](https://learn.microsoft.com/en-us/windows/win32/procthread/processor-groups),
[active processor count](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-getactiveprocessorcount).

Microsoft's ConPTY implementation starts a separate console-host process before
the attached application. A Job assigned only to the Docker CLI cannot claim to
bound this additional process. Raw streams avoid that process. A host ConPTY
route would require a broker already inside the helper Job before console
creation. The selected implementation instead relays Docker Engine's actual
container TTY through a private broker charged to the helper Job, avoiding a
redundant host console process.
[Microsoft implementation](https://github.com/microsoft/terminal/blob/main/src/winconpty/winconpty.cpp),
[session creation](https://learn.microsoft.com/en-us/windows/console/creating-a-pseudoconsole-session).

These are source design constraints, not Windows runtime qualification.
