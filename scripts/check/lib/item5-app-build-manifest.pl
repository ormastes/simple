#!/usr/bin/env perl
use strict;
use warnings;
use JSON::PP qw(decode_json);

sub fail {
    my ($message) = @_;
    die "$message\n";
}

sub load_json {
    my ($path) = @_;
    -f $path && -s $path <= 65536 or fail("provenance JSON missing/oversize");
    open my $fh, '<:raw', $path or fail("provenance JSON open failed");
    local $/;
    my $bytes = <$fh>;
    close $fh or fail("provenance JSON close failed");
    my $value = eval { decode_json($bytes) };
    $@ eq '' && ref($value) eq 'HASH' or fail("provenance JSON is not an object");
    return $value;
}

@ARGV >= 3 or fail("usage: item5-app-build-manifest.pl HELLO_JSON MANIFEST_JSON ROLE=SHA256...");
my ($hello_path, $manifest_path, @roles) = @ARGV;
my $hello = load_json($hello_path);
my $manifest = load_json($manifest_path);
($hello->{status} // '') eq 'pass' && ($hello->{gate_exit_status} // -1) == 0
    or fail("Phase2 Hello receipt is not PASS");

my $compiler = $hello->{compiler_sha256} // '';
my $producer_source = $hello->{source_commit} // '';
$compiler =~ /\A[0-9a-f]{64}\z/ && $producer_source =~ /\A[0-9a-f]{40,64}\z/
    or fail("Hello receipt lacks compiler/source provenance");
($manifest->{schema} // '') eq 'item5-simple-app-build-v2'
    or fail("app build manifest schema mismatch");
my $app_source = $manifest->{app_source_commit} // '';
my $app_tree = $manifest->{app_source_tree_oid} // '';
$app_source =~ /\A[0-9a-f]{40,64}\z/ && $app_tree =~ /\A[0-9a-f]{40,64}\z/
    or fail("app build manifest lacks app source commit/tree provenance");
($manifest->{compiler_sha256} // '') eq $compiler &&
    ($manifest->{producer_source_commit} // '') eq $producer_source
    or fail("app build manifest is not bound to the Hello producer");

for my $entry (@roles) {
    $entry =~ /\A([a-z][a-z0-9-]*)=([0-9a-f]{64})\z/
        or fail("invalid app role/hash argument");
    my ($role, $sha) = ($1, $2);
    my $app = $manifest->{apps}{$role} // {};
    ($app->{status} // '') eq 'pass' && ($app->{sha256} // '') eq $sha &&
        ($app->{compiler_sha256} // '') eq $compiler &&
        ($app->{app_source_commit} // '') eq $app_source &&
        ($app->{app_source_tree_oid} // '') eq $app_tree
        or fail("app build manifest mismatch for $role");
}
print join("\t", $compiler, $producer_source, $app_source, $app_tree), "\n";
