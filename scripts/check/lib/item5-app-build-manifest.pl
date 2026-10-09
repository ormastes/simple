#!/usr/bin/env perl
use strict;
use warnings;
use JSON::PP qw(decode_json);
use FindBin;
use lib $FindBin::Bin;
use Item5QemuProfile qw();

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

@ARGV >= 3 or fail("usage: item5-app-build-manifest.pl HELLO_JSON MANIFEST_JSON [target options] ROLE=SHA256...");
my ($hello_path, $manifest_path, @args) = @ARGV;
my %target_args;
while (@args && $args[0] =~ /^--/) {
    my $key = shift @args;
    @args or fail("missing value for $key");
    my $value = shift @args;
    $key =~ s/^--//;
    $key =~ /\A[a-z][a-z0-9-]*\z/ && !exists $target_args{$key}
        or fail("invalid or duplicate option --$key");
    $target_args{$key} = $value;
}
my @roles = @args;
@roles or fail("no app role hashes supplied");
my $hello = load_json($hello_path);
my $manifest = load_json($manifest_path);
my $gate_exit = $hello->{gate_exit_status};
defined($gate_exit) && !ref($gate_exit) && "$gate_exit" eq '0' &&
    ($hello->{status} // '') eq 'pass'
    or fail("Phase2 Hello receipt is not PASS");

my $compiler = $hello->{compiler_sha256} // '';
my $producer_source = $hello->{source_commit} // '';
$compiler =~ /\A[0-9a-f]{64}\z/ && $producer_source =~ /\A(?:[0-9a-f]{40}|[0-9a-f]{64})\z/
    or fail("Hello receipt lacks compiler/source provenance");
my $target_profile = $target_args{'target-profile'} // '';
my $target = exists $manifest->{target} && ref($manifest->{target}) eq 'HASH'
    ? $manifest->{target} : {};
my $is_target = length($target_profile) > 0;
if ($is_target) {
    my $profile = Item5QemuProfile::profile($target_profile)
        or fail("unsupported fixed QEMU target profile");
    ($manifest->{schema} // '') eq 'item5-simple-app-build-v3'
        or fail("target execution requires item5-simple-app-build-v3");
    my %required = map { $_ => 1 } qw(
        runtime-archive-sha256 toolchain-id sysroot-id sysroot-manifest-sha256
        provider-sha256 observer-sha256 qemu-sha256 qemu-version
        probe-compiler-sha256 probe-compiler-version
    );
    my %allowed = (%required, 'target-profile' => 1);
    for my $key (keys %target_args) {
        exists $allowed{$key} or fail("unexpected target option --$key");
    }
    for my $key (keys %required) {
        defined($target_args{$key}) && length($target_args{$key})
            or fail("target invocation lacks --$key");
    }
    for my $key (qw(runtime-archive-sha256 sysroot-manifest-sha256 provider-sha256
            observer-sha256 qemu-sha256 probe-compiler-sha256)) {
        $target_args{$key} =~ /\A[0-9a-f]{64}\z/
            or fail("invalid target hash for --$key");
    }
    for my $key (qw(toolchain-id sysroot-id qemu-version probe-compiler-version)) {
        length($target_args{$key}) <= 256 && $target_args{$key} !~ /[\r\n\0]/
            or fail("invalid target identity for --$key");
    }
    my %expected_target = (
        profile => $target_profile,
        triple => $profile->{triple},
        runtime_archive_sha256 => $target_args{'runtime-archive-sha256'},
        toolchain_id => $target_args{'toolchain-id'},
        sysroot_path => $profile->{sysroot},
        sysroot_id => $target_args{'sysroot-id'},
        sysroot_manifest_sha256 => $target_args{'sysroot-manifest-sha256'},
        provider_sha256 => $target_args{'provider-sha256'},
        observer_sha256 => $target_args{'observer-sha256'},
        qemu_sha256 => $target_args{'qemu-sha256'},
        qemu_version => $target_args{'qemu-version'},
        pid_probe_compiler_sha256 => $target_args{'probe-compiler-sha256'},
        pid_probe_compiler_version => $target_args{'probe-compiler-version'},
    );
    for my $key (keys %expected_target) {
        ($target->{$key} // '') eq $expected_target{$key}
            or fail("target manifest mismatch for $key");
    }
} else {
    ($manifest->{schema} // '') eq 'item5-simple-app-build-v2'
        or fail("native execution requires item5-simple-app-build-v2");
    keys(%target_args) == 0 or fail("target arguments require a target profile");
}
my $app_source = $manifest->{app_source_commit} // '';
my $app_tree = $manifest->{app_source_tree_oid} // '';
$app_source =~ /\A(?:[0-9a-f]{40}|[0-9a-f]{64})\z/ &&
    $app_tree =~ /\A(?:[0-9a-f]{40}|[0-9a-f]{64})\z/
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
    if ($is_target) {
        ($app->{target_profile} // '') eq $target_profile &&
            ($app->{target_triple} // '') eq $target->{triple} &&
            ($app->{runtime_archive_sha256} // '') eq $target->{runtime_archive_sha256}
            or fail("target app manifest mismatch for $role");
    }
}
print join("\t", $compiler, $producer_source, $app_source, $app_tree), "\n";
