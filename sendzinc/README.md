whif_sendzinc
=============

This library is very much a work in progress.  It provides an
interface to CP solvers and tools &mdash; very limited in scope and
lacking, so far, a clear plan of covering more problem classes,
dealing with over-constrained problems or postprocessing of solutions.
The focus is now on preprocessing of constraints.

In its current form, the library expects that a `minizinc` binary
(batteries included, see [_the MiniZinc
website_](https://www.minizinc.org/software.html))

  - is available as `$(which minizinc)`, unless it
  - may be found in `$(pwd)/../tools/MiniZincIDE/bin`, unless it
  - is installed under a path to a directory that was passed to an
    appropriate `with_minizinc` or `set_minizinc` call,

which is a runtime requirement, but may change, at some point, to a
compile time dependency.

## License

`whif_sendzinc` is licensed under the MIT license.  Please read the
[LICENSE-MIT](LICENSE-MIT) file in this repository for more
information.
