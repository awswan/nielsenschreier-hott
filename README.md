# A Formalisation of the Nielsen-Schreier Theorem in Homotopy Type Theory in Agda

The Nielsen-Schreier theorem states that subgroups of free groups are also free groups. This is a formalisation of the special case of finite index subgroups in homotopy type theory.

## Formalisation of the Theorem

The main theorem and the lemmas it uses are all in the directory `main/`. They use the HoTT-Agda library, which is *incompatible with the most recent versions of Agda*. The location of `hott-core.agda-lib` in the HoTT-Agda library needs to be listed in the [Agda libraries file](https://agda.readthedocs.io/en/v2.5.4.2/tools/package-system.html).

The main theorem has been tested and type checks successfully with the following setup:

- Agda version 2.5.4.2
- [HoTT-Agda commit 7e62770](https://github.com/HoTT/HoTT-Agda/tree/7e62770e9f2a8df4053f8936de369b9554668dcf)

## Demonstration of Cubical Mode

Some of the lemmas on coequalizers have shorter proofs using Agda cubical mode. The file `cubical/Coequalizers.agda` has been added to demonstrate this. Since this file uses cubical mode, it *only* works on the most recent versions of Agda. It has been tested and type checks successfully on the following setup (but likely will continue to work on more recent versions):

- Agda 2.6.1
- [Cubical Agda library v0.2](https://github.com/agda/cubical/releases/tag/v0.2)
