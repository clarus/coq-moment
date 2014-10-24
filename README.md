# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/watch-48.png) Moment
Parse, manipulate and pretty-print dates in Coq.

    Require Import Coq.Strings.String.
    Require Import FunctionNinjas.All.
    Require Import ListString.All.
    Require Import Moment.All.

    Compute LString.to_string @@ Moment.PrettyPrint.rfc1123 @@ Moment.of_epoch 0.

gives:
    
    "Thu, 01 Jan 1970 00:00:00 GMT"%string

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

at the beginning of your source files. It will add three new modules:
* `Date`: day in a calendar
* `Time`: time in a day
* `Moment`: a date and a time