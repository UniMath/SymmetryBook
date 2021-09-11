$pdf_mode = 1;

$pdflatex = "pdflatex -halt-on-error -synctex=1 --shell-escape -fmt macros %O %S";

@default_files = ("book");

push @generated_exts, "glo", "gls";

add_cus_dep("glo", "gls", 0, glo2gls);

sub glo2gls {
    return system( "makeindex -s cas.gst -o \"$_[0].gls\" \"$_[0].glo\"" );
}
