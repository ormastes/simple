package BootstrapNativeImage;
use strict;
use warnings;
use Exporter 'import';
our @EXPORT_OK = qw(verify_native_image verify_native_object);

sub read_at {
    my ($fh, $size, $offset, $count) = @_;
    $offset >= 0 && $count >= 0 && $offset <= $size && $count <= $size - $offset
        or die "native image range outside file\n";
    seek($fh, $offset, 0) or die "native image seek failed\n";
    read($fh, my $bytes, $count) == $count or die "native image truncated\n";
    return $bytes;
}

# Validate the container and host machine, not compiler correctness or admission.
# Read only bounded headers even when the executable is hundreds of megabytes.
sub verify_native_image {
    my ($path, $system, $machine) = @_;
    -f $path && !-l $path && -x $path or die "native product missing or not executable\n";
    open my $fh, '<:raw', $path or die "cannot inspect native product\n";
    my $size = -s $fh;
    my $header = read_at($fh, $size, 0, 64);
    if ($system =~ /\A(?:Linux|FreeBSD)\z/) {
        substr($header, 0, 4) eq "\x7fELF" && ord(substr($header, 4, 1)) == 2 &&
            ord(substr($header, 5, 1)) == 1 &&
            (unpack('v', substr($header, 16, 2)) == 2 || unpack('v', substr($header, 16, 2)) == 3)
            or die "product is not a host ELF executable image\n";
        my %machines = (x86_64 => 62, amd64 => 62, aarch64 => 183, arm64 => 183);
        exists($machines{lc $machine}) && unpack('v', substr($header, 18, 2)) == $machines{lc $machine}
            or die "product ELF machine differs from host target\n";
    } elsif ($system =~ /\A(?:MSWin32|Windows_NT|(?:MINGW|MSYS|CYGWIN)[^\s]*)\z/i) {
        substr($header, 0, 2) eq 'MZ' or die "product has no DOS/PE header\n";
        my $pe_offset = unpack('V', substr($header, 60, 4));
        $pe_offset >= 64 or die "PE header overlaps DOS header\n";
        my $coff = read_at($fh, $size, $pe_offset, 24);
        substr($coff, 0, 4) eq "PE\0\0" or die "product PE signature differs\n";
        my ($arch, $sections) = unpack('vv', substr($coff, 4, 4));
        my ($optional_size, $flags) = unpack('vv', substr($coff, 20, 4));
        my %machines = (x86_64 => 0x8664, amd64 => 0x8664, aarch64 => 0xaa64, arm64 => 0xaa64);
        exists($machines{lc $machine}) && $arch == $machines{lc $machine}
            or die "product PE machine differs from host target\n";
        ($flags & 0x0002) && !($flags & 0x2000) && !($flags & 0x0100)
            or die "product is not a PE64 executable (DLL/object/32-bit image)\n";
        $sections >= 1 && $sections <= 96 && $optional_size >= 112 && $optional_size <= 4096
            or die "invalid PE header dimensions\n";
        my $optional = read_at($fh, $size, $pe_offset + 24, $optional_size);
        unpack('v', $optional) == 0x20b or die "product optional header is not PE32+\n";
        my $entry = unpack('V', substr($optional, 16, 4));
        my ($image_size, $headers_size) = unpack('VV', substr($optional, 56, 8));
        my $section_offset = $pe_offset + 24 + $optional_size;
        $entry > 0 && $entry < $image_size && $headers_size >= $section_offset + 40 * $sections &&
            $headers_size <= $size && $image_size > $headers_size
            or die "invalid PE entry/image/header extent\n";
        my $table = read_at($fh, $size, $section_offset, 40 * $sections);
        my $entry_in_code = 0;
        for my $i (0 .. $sections - 1) {
            my $section = substr($table, $i * 40, 40);
            my ($virtual_size, $rva, $raw_size, $raw_offset) = unpack('VVVV', substr($section, 8, 16));
            my $section_flags = unpack('V', substr($section, 36, 4));
            my $span = $virtual_size > $raw_size ? $virtual_size : $raw_size;
            $rva <= $image_size && $span <= $image_size - $rva
                or die "PE section outside image\n";
            if ($raw_size) {
                $raw_offset >= $headers_size && $raw_offset <= $size && $raw_size <= $size - $raw_offset
                    or die "PE section bytes outside file\n";
            }
            # Entry must address actual file-backed executable bytes, not BSS.
            $entry_in_code = 1 if ($section_flags & 0x20000000) && $entry >= $rva &&
                $entry - $rva < $raw_size;
        }
        $entry_in_code or die "PE entry has no executable section bytes\n";
    } else {
        die "native product host unsupported by this gate\n";
    }
    close $fh or die "cannot close native product\n";
    return 1;
}
# Diagnostic objects prove target/container identity only, never bootstrap PASS.
# An undefined path validates the requested target before any compiler starts.
sub verify_native_object {
    my ($path, $target) = @_;
    my ($arch, $format);
    $target =~ /\A(x86_64|aarch64|i686|armv7|riscv64)-[a-z0-9_.-]+\z/
        or die "unsupported diagnostic object target\n";
    $arch = $1;
    my $platform = substr($target, length($arch) + 1);
    $format = $platform =~ /\A(?:(?:unknown-)?linux-(?:gnu|musl)(?:eabi|eabihf)?|(?:unknown-)?freebsd(?:[0-9.]+)?|(?:unknown-)?none(?:-elf|-eabi|-eabihf)?)\z/ ? 'elf' :
        $platform =~ /\A(?:pc-)?windows-(?:gnu|msvc)\z/ ? 'coff' :
        $platform =~ /\Aapple-(?:darwin|macos)\z/ ? 'macho' : '';
    $format ne '' or die "unsupported diagnostic object format\n";
    my %machines = (x86_64 => 62, aarch64 => 183, i686 => 3, armv7 => 40, riscv64 => 243);
    my %coff = (x86_64 => 0x8664, aarch64 => 0xaa64, i686 => 0x14c, armv7 => 0x1c4);
    my %macho = (x86_64 => 0x1000007, aarch64 => 0x100000c);
    ($format ne 'coff' || exists $coff{$arch}) &&
        ($format ne 'macho' || exists $macho{$arch}) or die "unsupported target architecture\n";
    return 1 unless defined $path;
    -f $path && !-l $path or die "diagnostic object missing or symlinked\n";
    open my $fh, '<:raw', $path or die "cannot open diagnostic object\n";
    my $size = -s $fh;
    my $h = read_at($fh, $size, 0, 64);
    if ($format eq 'elf') {
        my $class = ($arch eq 'i686' || $arch eq 'armv7') ? 1 : 2;
        substr($h, 0, 4) eq "\x7fELF" && ord(substr($h, 4, 1)) == $class &&
            ord(substr($h, 5, 1)) == 1 && unpack('v', substr($h, 16, 2)) == 1 &&
            unpack('v', substr($h, 18, 2)) == $machines{$arch}
            or die "diagnostic object ELF type/class/machine differs from target\n";
        my $offset = $class == 2 ? unpack('Q<', substr($h, 40, 8)) : unpack('V', substr($h, 32, 4));
        my ($width, $count) = unpack('vv', substr($h, $class == 2 ? 58 : 46, 4));
        $offset > 0 && $width == ($class == 2 ? 64 : 40) && $count > 1 &&
            $offset <= $size && $count * $width <= $size - $offset
            or die "diagnostic object ELF section table missing or truncated\n";
    } elsif ($format eq 'coff') {
        my ($machine, $count) = unpack('vv', $h);
        $machine == $coff{$arch} && $count > 0 && unpack('v', substr($h, 16, 2)) == 0 &&
            20 + 40 * $count <= $size or die "diagnostic object COFF target/table differs\n";
    } else {
        unpack('V', $h) == 0xfeedfacf && unpack('V', substr($h, 4, 4)) == $macho{$arch} &&
            unpack('V', substr($h, 12, 4)) == 1 && unpack('V', substr($h, 16, 4)) > 0 &&
            32 + unpack('V', substr($h, 20, 4)) <= $size
            or die "diagnostic object Mach-O target/type/table differs\n";
    }
    close $fh or die "cannot close diagnostic object\n";
    return 1;
}
1;
