#ifndef SIMPLE_COSMOS_STORAGE_POLICY_H
#define SIMPLE_COSMOS_STORAGE_POLICY_H

/* Native acquisition calls consumed only by cosmos_storage_policy.spl. */
int cosmos_storage_bridge_is_qemu(void);
int cosmos_storage_bridge_backend_init(void);
int cosmos_storage_bridge_ftl_init(void);
int cosmos_storage_bridge_backend_mount(void);
int cosmos_storage_bridge_ftl_recover(void);
int cosmos_storage_bridge_media_init(void);
int cosmos_storage_bridge_io_init(void);
int cosmos_storage_bridge_admin_init(void);
int cosmos_storage_bridge_dispatch_init(void);
int cosmos_storage_bridge_backend_format(void);
int cosmos_storage_bridge_factory_initialize_erased(void);
int cosmos_storage_bridge_dispatch_poll(void);
int cosmos_storage_bridge_gc_step(void);

#endif
