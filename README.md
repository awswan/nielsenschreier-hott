# A Formalisation of the Nielsen-Schreier Theorem in Homotopy Type Theory in Agda

The Nielsen-Schreier theorem states that subgroups of free groups are also free groups. This is a formalisation of the special case of finite index subgroups in homotopy type theory.

## Formalisation of the Theorem

The main theorem and the lemmas it uses are all in the directory `main/`, using a forked version of the HoTT-Agda library.

### Type Checking

Follow these steps to check the proof in Agda:

1. Install a recent version of the [Agda proof assistant](https://agda.readthedocs.io/en/v2.6.1.1/getting-started/installation.html). This method has been tested with versions 2.6.1 and 2.6.1.1.

2. Download the forked version of the HoTT-Agda library from https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible to a directory of your choice. If you have git installed, you can also use the command `git clone -b agda-2.6.1-compatible git@github.com:awswan/HoTT-Agda.git`.

3. Add the location of the file `hott-core.agda-lib` to your [Agda library file](https://agda.readthedocs.io/en/v2.6.1.1/tools/package-system.html).

4. Change to the directory `main/` of this repository and run `agda NielsenSchreier.agda` to type check the theorem.

You can alternatively use a non-forked version of the [HoTT-Agda library](https://github.com/HoTT/HoTT-Agda). Note however that this is *incompatible with the most recent versions of Agda*. To do this you will need to delete the option `--overlapping-instances` from the header of the files `Groups/Definition.agda`, `Util/Misc.agda` and `NielsenSchreier.agda`.

This has been tested and type checks successfully with the following setup:

- Agda version 2.5.4.2
- [HoTT-Agda commit 7e62770](https://github.com/HoTT/HoTT-Agda/tree/7e62770e9f2a8df4053f8936de369b9554668dcf)

### Directory Layout

The files are arrange as follows:
- `main/NielsenSchreier.agda` Contains proof of the main theorem
- `main/Coequalizers/` Definition of coequalizers and some useful lemmas
- `main/Graphs/` Definition of graphs, trees and connected graphs, construction of spanning trees for graphs with finitely many vertices
- `main/Groups/` Type theoretic definition of group and free group
- `main/Util/` Some general miscellaneous lemmas that I couldn't find in the HoTT-Agda library

## Demonstration of Cubical Mode

Some of the lemmas on coequalizers have shorter proofs using Agda cubical mode. The file `cubical/Coequalizers.agda` has been added to demonstrate this. Since this file uses cubical mode, it only works on the most recent versions of Agda. It has been tested and type checks successfully on the following setup (but likely will continue to work on more recent versions):

- Agda 2.6.1
- [Cubical Agda library v0.2](https://github.com/agda/cubical/releases/tag/v0.2)
