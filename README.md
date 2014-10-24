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

## Reference
### Date
* `t` A date is a year, a month and a day. There is no enforced bound by the type system for the month and the day number, but values are expected to be in the standard range.  he month and day number start at one. A date can be of Julian or Gregorian calendar, depending on the context.
* `compare (date1 date2 : t) : comparison` Compare two dates.
* `of_Julian_day (is_Gregorian : bool) (n : Z) : t` The date of a Julian day, in a Julian or Gregorian calendar.
* `to_Julian_day (is_Gregorian : bool) (date : t) : Z` The Julian day of a date, considering the date as Julian or Gregorian.
* `epoch : t` The Unix epoch (in the Gregorian calendar).
* `of_epoch (n : Z) : t` The Gregorian date of a Unix day.
* `to_epoch (date : t) : Z` The Unix day of a Gregorian date.

### Date.WeekDay
* `t` The finite set of days of the week.
* `of_Z (n : Z) : t` 0 for Sunday, 1 for Monday, ...
* `of_date (is_Gregorian : bool) (date : Date.t) : t` The day of the week of a date.

### Date.WeekDay.PrettyPrint
* `full (day : t) : LString.t` The full name of a day of the week (Monday, Tuesday, ...).
* `short (day : t) : LString.t` The short name of a day of the week (Mon, Tue, ...).

### Date.Month
* `t` : The finite set of months.
* `of_Z (n : Z) : t` : 1 for January, 2 for February, ...
* `of_date (date : Date.t) : t` : The month of a date.

### Date.Month.PrettyPrint
* `full (month : t) : LString.t` : The full name of a month (January, February, ...).
* `short (month : t) : LString.t` : The short name of a month (Jan, Feb, ...).

### Date.PrettyPrint
* `year (date : t) : LString.t` : The year.
* `month (date : t) : LString.t` : The month number.
* `space_padded_month (date : t) : LString.t` : The month number with space padding.
* `zero_padded_month (date : t) : LString.t` : The month number with zero padding.
* `day (date : t) : LString.t` : The day number.
* `space_padded_day (date : t) : LString.t` : The day number with space padding.
* `zero_padded_day (date : t) : LString.t` : The day number with zero padding.
* `full_week_day (is_Gregorian : bool) (date : t) : LString.t` : The full name of a day of the week (Monday, Tuesday, ...).
* `short_week_day (is_Gregorian : bool) (date : t) : LString.t` : The short name of a day of the week (Mon, Tue, ...).
* `full_month (date : t) : LString.t` : The full name of a month (January, February, ...).
* `short_month (date : t) : LString.t` : The short name of a month (Jan, Feb, ...).
