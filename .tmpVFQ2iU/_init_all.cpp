// Auto-generated: calls all __module_init_* functions
extern "C" {
    void __attribute__((weak)) __module_init_common__error_codes(void);
    void __attribute__((weak)) __module_init_common__fault_detection(void);
    void __attribute__((weak)) __module_init_common__gc_boundary(void);
    void __attribute__((weak)) __module_init_common__text(void);
    void __attribute__((weak)) __module_init_frontend__core__lexer(void);
    void __attribute__((weak)) __module_init_mcp__assistant__session_store(void);
    void __attribute__((weak)) __module_init_mcp__assistant__session_views(void);
    void __attribute__((weak)) __module_init_mcp__main(void);
    void __attribute__((weak)) __module_init_mcp__main_lazy_assistant(void);
    void __attribute__((weak)) __module_init_mcp__main_lazy_debug_tools(void);
    void __attribute__((weak)) __module_init_mcp__main_lazy_diag_tools(void);
    void __attribute__((weak)) __module_init_mcp__main_lazy_dialog_tools(void);
    void __attribute__((weak)) __module_init_mcp__main_lazy_protocol(void);
    void __attribute__((weak)) __module_init_mcp__main_lazy_vcs_tools(void);
}
extern "C" void __simple_call_module_inits(void) {
    if (__module_init_common__error_codes) __module_init_common__error_codes();
    if (__module_init_common__fault_detection) __module_init_common__fault_detection();
    if (__module_init_common__gc_boundary) __module_init_common__gc_boundary();
    if (__module_init_common__text) __module_init_common__text();
    if (__module_init_frontend__core__lexer) __module_init_frontend__core__lexer();
    if (__module_init_mcp__assistant__session_store) __module_init_mcp__assistant__session_store();
    if (__module_init_mcp__assistant__session_views) __module_init_mcp__assistant__session_views();
    if (__module_init_mcp__main) __module_init_mcp__main();
    if (__module_init_mcp__main_lazy_assistant) __module_init_mcp__main_lazy_assistant();
    if (__module_init_mcp__main_lazy_debug_tools) __module_init_mcp__main_lazy_debug_tools();
    if (__module_init_mcp__main_lazy_diag_tools) __module_init_mcp__main_lazy_diag_tools();
    if (__module_init_mcp__main_lazy_dialog_tools) __module_init_mcp__main_lazy_dialog_tools();
    if (__module_init_mcp__main_lazy_protocol) __module_init_mcp__main_lazy_protocol();
    if (__module_init_mcp__main_lazy_vcs_tools) __module_init_mcp__main_lazy_vcs_tools();
}
