whif_sendzinc
=============

This library provides a very limited interface to CP solvers and
tools.  In its current form it expects that a `minizinc` binary
(batteries included, see [_the MiniZinc
website_](https://www.minizinc.org/software.html)) is installed

  - in `$(which minizinc)`,
  - unless it may be found in `$(pwd)/../tools/MiniZincIDE/bin`,
  - unless a path to a directory was passed to an appropriate
    `with_minizinc` or `set_minizinc` call.

This is very much a work in progress.

## License

`whif_sendzinc` is licensed under the MIT license.  Please read the
[LICENSE-MIT](LICENSE-MIT) file in this repository for more
information.
