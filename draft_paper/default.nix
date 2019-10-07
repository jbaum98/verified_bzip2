{ compileTex, texlive, iosevka-bin }:
let
  tex = texlive.combine ({
    inherit (texlive)
    amscls
    amsfonts
    amsmath
    biber
    biblatex
    biblatex-ieee
    boondox
    caption
    cleveref
    cm-super
    cmap
    collection-fontsrecommended
    comment
    draftwatermark
    enumitem
    environ
    epsf
    etoolbox
    euenc
    eulervm
    fancyhdr
    float
    fontaxes
    fontspec
    geometry
    graphics
    graphics-def
    hyperref
    ifluatex
    ifxetex
    inconsolata
    kastrup
    latexmk
    libertine
    listings
    lkproof
    logreq
    mathpazo
    mathtools
    microtype
    mmap
    ms
    mweights
    natbib
    ncctools
    newtx
    oberdiek
    paralist
    parskip
    realscripts
    scheme-basic
    setspace
    sourcesanspro
    textcase
    thmtools
    titlesec
    totpages
    trimspaces
    upquote
    url
    xcolor
    xetex
    xkeyval
    xltxtra
    xstring
    ;
  });
in compileTex {
  srcDir = ./.;
  texFile = "draft_paper.tex";
  otherFiles = [ "acmart.cls" "ACM-Reference-Format.bst" "draft_paper.bib" "thesis.cls" "lstlangcoq.sty" ];
  fonts = [ iosevka-bin ];
  inherit tex;
}
