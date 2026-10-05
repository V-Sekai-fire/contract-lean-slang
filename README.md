# contract-lean-slang

A Lean 4 library that builds a Slang shader AST and prints it as source text, with a check that the text compiles to SPIR-V.

## What it is for

It lets a compute kernel be written and checked in Lean and emitted as a shader, rather than
hand-ported from a separate spec. Reference fixtures are asserted when the library builds, so a
change to the printer fails the build, and an end-to-end check compiles the emitted text in
process. RFD 2032 owns the design.

## Build

```sh
vendor/fetch.sh
lake build
```

The fetch downloads the Slang SDK the compile check links. Another Lake package depends on it
with:

```lean
require LeanSlang from git "https://github.com/V-Sekai-fire/contract-lean-slang.git"
```

## Licence

MIT; see `LICENSE`.
