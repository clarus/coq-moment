# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/watch-48.png) Moment
> Parse, manipulate and pretty-print times and dates in Coq.

[![Build Status](https://travis-ci.com/clarus/coq-moment.svg?branch=master)](https://travis-ci.com/clarus/coq-moment)

Example:
```coq
Require Import Coq.Strings.String.
Require Import ListString.All.
Require Import Moment.All.

Compute LString.to_string (Moment.Print.rfc1123 (Moment.of_epoch 0)).
```
gives:
```coq
"Thu, 01 Jan 1970 00:00:00 GMT"%string
```

## Install
### With opam
Using the package manager [opam](https://opam.ocaml.org/), add the [Coq repository](https://github.com/coq/opam-coq-archive):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-moment

### Manually
Read the `coq-moment.opam` file to know the dependencies of the project and get the install commands.

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

### Date.WeekDay.Print
* `full (day : t) : LString.t` The full name of a day of the week (Monday, Tuesday, ...).
* `short (day : t) : LString.t` The short name of a day of the week (Mon, Tue, ...).

### Date.WeekDay.Parse
* `full (s : LString.t) : option (t * LString.t)` Parse the full name of a day of the week (Monday, Tuesday, ...).
* `short (s : LString.t) : option (t * LString.t)` Parse the short name of a day of the week (Mon, Tue, ...).

### Date.Month
* `t` The finite set of months.
* `of_Z (n : Z) : t` 1 for January, 2 for February, ...
* `of_date (date : Date.t) : t` The month of a date.

### Date.Month.Print
* `full (month : t) : LString.t` The full name of a month (January, February, ...).
* `short (month : t) : LString.t` The short name of a month (Jan, Feb, ...).

### Date.Month.Parse
* `full (s : LString.t) : option (t * LString.t)` Parse the full name of a month (January, February, ...).
* `short (s : LString.t) : option (t * LString.t)` Parse the short name of a month (Jan, Feb, ...).

### Date.Print
* `year (digits : nat) (padding : option Ascii.ascii) (date : t) : LString.t` The year, supposed to be positive, with an optional padding to be of width `digits`.
* `month month (padding : option Ascii.ascii) (date : t) : LString.t` The month number, with an optional padding to be of width two.
* `day day (padding : option Ascii.ascii) (date : t) : LString.t` The day number, with an optional padding to be of width two.
* `full_week_day (is_Gregorian : bool) (date : t) : LString.t` The full name of the day of the week (Monday, Tuesday, ...).
* `short_week_day (is_Gregorian : bool) (date : t) : LString.t` The short name of the day of the week (Mon, Tue, ...).
* `full_month (date : t) : LString.t` The full name of the month (January, February, ...).
* `short_month (date : t) : LString.t` The short name of the month (Jan, Feb, ...).
* `date (date : t) : LString.t` The date in the format yyyy-mm-dd.

### Date.Parse
* `zero_padded_year (digits : nat) (s : LString.t) : option (Z * LString.t)` Parse a year with a fixed number of digits.
* `zero_padded_month (s : LString.t) : option (Z * LString.t)` Parse a month number with two digits.
* `zero_padded_day (s : LString.t) : option (Z * LString.t)` Parse a day number with two digits.
* `date (s : LString.t) : option (t * LString.t)` Parse a date in the format yyyy-mm-dd.

### Time
* `t` A time is an hour, a minute and a second. There is no enforced bound by the type system, but values are expected to be in the standard range.
* `of_seconds (n : Z) : t` The time of a second number (the number of seconds since midnight).
* `to_seconds (time : t) : Z` The number of seconds since midnight of a time.

### Time.Print
* `hour (padding : option Ascii.ascii) (time : t) : LString.t` Pretty-print the hour number, with an optional padding to be of width two.
* `minute (padding : option Ascii.ascii) (time : t) : LString.t` Pretty-print the minute number, with an optional padding to be of width two.
* `second (padding : option Ascii.ascii) (time : t) : LString.t` Pretty-print the second number, with an optional padding to be of width two.
* `time (time : t) : LString.t` The time in the format hh:mm:ss.

### Time.Parse
* `time (s : LString.t) : option (t * LString.t)` Parse a time in the format hh:mm:ss.
* `time_zone_offset (s : LString.t) : option (t * LString.t)` Parse a time zone offset, +hh:mm or -hh:mm.

### Moment
* `t` A moment is a date and a time.
* `of_epoch (n : Z) : t` The moment given by a number of seconds since the Unix epoch.
* `to_epoch (moment : t) : Z` The number of seconds since the Unix epoch.

### Moment.Print
* `rfc1123 (moment : t) : LString.t` The moment in the RFC 1123 format, like `Sun, 06 Nov 1994 08:49:37 GMT`.
* `rfc3339 (moment : t) : LString.t` The moment in the RFC 3339 format, like `2002-10-02T15:00:00Z`.

### Moment.Parse
* `rfc3339 (s : LString.t) : option (t * LString.t)` Parse a moment in RFC 3339 format, like `2002-10-02T15:00:00Z`. We ignore the optional decimal part of the seconds.
