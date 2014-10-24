# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/watch-48.png) Moment
Parse, manipulate and pretty-print dates in Coq.

## Install
### With OPAM
Add the Coq repository:

    opam repo add coq-stable https://github.com/coq/repo-stable.git

and run:

    opam install coq-moment

### From the sources
Do a classic:

    ./configure.sh
    make
    make install

## Use
Add:

    Require Import Moment.All.

at the beginning of your source files.