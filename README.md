# Base Library of the Albatross Compiler

## Installation

The installation of the library requires the installation of the [Albatross
compiler](https://github.com/hbr/albatross).

- Download the .zip or .tgz file and unpack it. The library shall unpack into
  a directory called `alba.base`. Make sure the directory has exactly this
  name. If it unpacks e.g. to `alba.base-master`, then rename it to
  `alba.base`.
- `cd alba.base`
- `alba init`
- `alba compile`


Now you have a compiled version of the base library.

Then go to the source directory of your Albatross program and issue `alba
compile -I <path-to-dir-above-alba.base>` to compile your Albatross sources.
