# Architecture: SimpleOS filesystem toolchain and servers

## Decision

Keep one owner per boundary:

```text
QEMU request -> boot TCP facade -> HTTP default or POST /db service
mounted VFS file -> executable range reader -> ELF PT_LOAD mapper -> user task
target Simple payload -> install image role list -> compiler/interpreter/loader paths
```

The loader opens the requested canonical path, reads the ELF header/program
headers, allocates pages, and fills each `PT_LOAD` range with bounded reads. It
does not cache or substitute executable bytes; the old global preload is outside
the hosted launch path.

The existing single HTTP listener remains the only network owner. `POST /db`
dispatches to one persistent bounded database service; all other requests keep
the existing HTTP response path. A second listener and scheduler are unnecessary
for the selected request/response proof.

The DB scenario uses existing Pure Simple parsing/storage primitives where the
freestanding closure supports them; otherwise its smallest owner-layer service
implements only the selected bounded create/insert/select protocol and is not
presented as the full historical `simple_db` product.

GOT residency remains an explicit bare-metal optimization. Hosted SimpleOS,
Clang, Simple compiler, interpreter, and loader all use filesystem provenance.
