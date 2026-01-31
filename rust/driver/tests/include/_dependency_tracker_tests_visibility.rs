// Feature #114: Visibility Export Tests
// =============================================================================

#[test]
fn visibility_private_symbol_stays_private() {
    // Formal model theorem: private_stays_private
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::public("mymodule"));
    manifest.add_export(SymbolId::new("foo"));

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::private("foo")); // Private symbol

    let sym = SymbolId::new("foo");
    let vis = effective_visibility(&manifest, "mymodule", &mc, &sym);

    assert_eq!(vis, Visibility::Private);
}

#[test]
fn visibility_private_module_restricts() {
    // Formal model theorem: private_module_restricts
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::private("internal")); // Private module
    manifest.add_export(SymbolId::new("Helper"));

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::public("Helper"));

    let sym = SymbolId::new("Helper");
    let vis = effective_visibility(&manifest, "internal", &mc, &sym);

    // Even though symbol is public and exported, module is private
    assert_eq!(vis, Visibility::Private);
}

#[test]
fn visibility_must_be_exported() {
    // Formal model theorem: must_be_exported
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::public("router"));
    // NOT adding export for "Helper"

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::public("Helper"));

    let sym = SymbolId::new("Helper");
    let vis = effective_visibility(&manifest, "router", &mc, &sym);

    // Public module, public symbol, but not exported
    assert_eq!(vis, Visibility::Private);
}

#[test]
fn visibility_fully_public() {
    // All conditions met: public module + public symbol + exported
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::public("router"));
    manifest.add_export(SymbolId::new("Router"));

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::public("Router"));

    let sym = SymbolId::new("Router");
    let vis = effective_visibility(&manifest, "router", &mc, &sym);

    assert_eq!(vis, Visibility::Public);
}

#[test]
fn visibility_ancestor_chain() {
    // Formal model theorems: any_private_means_private, all_public_means_public

    // All public ancestors
    let path = vec![Visibility::Public, Visibility::Public, Visibility::Public];
    assert_eq!(ancestor_visibility(&path), Visibility::Public);

    // One private ancestor
    let path = vec![Visibility::Public, Visibility::Private, Visibility::Public];
    assert_eq!(ancestor_visibility(&path), Visibility::Private);

    // Empty path (root) is public
    assert_eq!(ancestor_visibility(&[]), Visibility::Public);
}

#[test]
fn visibility_meet_properties() {
    // Formal model theorems: meet_comm, meet_assoc

    // Commutative
    assert_eq!(
        visibility_meet(Visibility::Public, Visibility::Private),
        visibility_meet(Visibility::Private, Visibility::Public)
    );

    // Associative
    let a = Visibility::Public;
    let b = Visibility::Private;
    let c = Visibility::Public;
    assert_eq!(
        visibility_meet(visibility_meet(a, b), c),
        visibility_meet(a, visibility_meet(b, c))
    );

    // Private absorbs
    assert_eq!(
        visibility_meet(Visibility::Private, Visibility::Public),
        Visibility::Private
    );

    // Public is identity
    assert_eq!(
        visibility_meet(Visibility::Public, Visibility::Public),
        Visibility::Public
    );
}

// =============================================================================
