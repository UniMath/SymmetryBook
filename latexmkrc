@default_files = ("book");

push @generated_exts, "glo", "gls";

add_cus_dep("glo", "gls", 0, glo2gls);

sub glo2gls {
    return system( "makeindex -s cas.gst -o \"$_[0].gls\" \"$_[0].glo\"" );
}
