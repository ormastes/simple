# While-val introduces an unresolved synthetic true identifier

Native failure: producer 6d0b845e6e67e070f7872d8485284a247ecf27b8f4ddad168a1db7ef08fedb6b / source c9cb4ecbbd82713518a3b7cf0cf0a43f0be824cb rejects unchanged if_val_payload_owner_probe/main.spl at line22 during HIR: unresolved name true. No runtime assertion ran. Evidence: /mnt/c/Temp/simple-if-val-payload-owner-evidence-20261010/validation/optional_binding_runtime/build.log.

The simple while-val parser branch injects expr_ident("true",0), while ordinary boolean syntax and the nearby let-else loop guard use expr_bool_lit(1,0). Replacing only that synthetic condition with the real boolean node fixes its source authority without declaring a fake true variable or altering the fixture. Evaluation order, marked binding, condition refresh and break behavior are unchanged.

Status: proposed repair UNEXECUTED. Parser spec requires actual BoolLit and retained bind_optional_payload on the nested initializer. Next native criterion reruns the unchanged primitive present/absent/while/single-evaluation fixture under a newly pinned producer. The earlier invalid-array-handle diagnostic is separately retained; no causal claim ties it to this boolean node and it must not be concealed by this repair.
