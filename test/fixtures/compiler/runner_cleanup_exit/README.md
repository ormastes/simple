# Runner cleanup and exit (#3077)

Compile the real cleanup_and_exit path, then require process status 23 and
stdout containing `Cleanup complete (0 resources)`. Status 0 or 99 is failure.
This standalone fixture begins with empty tracker state and starts no child or
container. Object proof alone is not exit-behavior proof. Execution is pending.
