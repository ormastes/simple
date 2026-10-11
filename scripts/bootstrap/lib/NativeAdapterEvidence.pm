package NativeAdapterEvidence;
use strict;
use warnings;
use Exporter 'import';
use Digest::SHA qw(sha256_hex);
use JSON::PP qw(decode_json);
use File::Basename qw(dirname);
our @EXPORT_OK = qw(build_evidence previous_build_evidence);

sub bytes {
    my ($path) = @_;
    -f $path && !-l $path or die "missing/linked build evidence: $path\n";
    open my $f, '<:raw', $path or die $!;
    local $/; return <$f>;
}

sub build_evidence {
    my ($root, $legacy) = @_;
    my $body = bytes("$root/build.env");
    my %fields;
    for my $line (split /\n/, $body) {
        $line =~ /\A([a-zA-Z_][a-zA-Z_0-9]*)=([^\r\n\0]*)\z/
            or die "malformed build field\n";
        !exists($fields{$1}) or die "duplicate build field: $1\n";
        $fields{$1} = $2;
    }
    my $schema = $legacy ? 'simple-restricted-native-adapter-build-v1' : 'simple-restricted-prefix-build-v1';
    ($fields{schema}//'') eq $schema && ($fields{formal_product_pass}//'') eq '0'
        or die "incorrect build authority\n";
    ($fields{backend}//'') =~ /\A(?:llvm|cranelift)\z/ or die "invalid build backend\n";
    ($fields{compiler_sha256}//'') =~ /\A[0-9a-f]{64}\z/ or die "invalid build producer\n";
    ($fields{runtime_capsule_sha256}//'') =~ /\A[0-9a-f]{64}\z/ or die "invalid build runtime capsule\n";
    my $workspace = $fields{$legacy ? 'source_root' : 'workspace'} // '';
    $workspace =~ m{\A/} or die "invalid build workspace\n";
    if (!$legacy) {
        ($fields{manifest_sha256}//'') eq sha256_hex(bytes("$root/manifest.json"))
            or die "build manifest differs\n";
        ($fields{runtime_cwd}//'') eq $workspace or die "build runtime workspace differs\n";
    }
    return {build_sha256=>sha256_hex($body), workspace=>$workspace,
        compiler_sha256=>$fields{compiler_sha256}, backend=>$fields{backend},
        runtime_capsule_sha256=>$fields{runtime_capsule_sha256}};
}

sub previous_build_evidence {
    my ($result_path, $workspace, $compiler_sha256, $backend, $runtime_capsule_sha256) = @_;
    my $result = decode_json(bytes($result_path));
    my $legacy = ($result->{schema}//'') eq 'simple-restricted-native-adapter-result-v1';
    $legacy || ($result->{schema}//'') eq 'simple-restricted-prefix-result-v1'
        or die "unsupported previous result\n";
    my $build = build_evidence(dirname($result_path), $legacy);
    for my $pair ([workspace=>$workspace], [compiler_sha256=>$compiler_sha256], [backend=>$backend],
            [runtime_capsule_sha256=>$runtime_capsule_sha256]) {
        $build->{$pair->[0]} eq $pair->[1] or die "previous build $pair->[0] differs\n";
    }
    if (!$legacy) {
        for my $key (qw(build_sha256 workspace compiler_sha256 backend runtime_capsule_sha256)) {
            ($result->{$key}//'') eq $build->{$key} or die "previous result $key differs\n";
        }
    }
    return $build;
}

1;
