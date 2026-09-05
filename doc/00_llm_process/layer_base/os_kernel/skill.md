# OS Kernel Layer Base

`src/os/kernel/**` is MDSOC-only. Do not introduce ECS or MDSOC+ business-world
state. Preserve capsule, architecture, interrupt, memory, and scheduler owners.
