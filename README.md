# Formal Verification of Saber (in EasyCrypt)
This repository corresponds to the master's thesis "Formal Verification of Saber", authored by M.C.F.H.P. Meijers.\
\
Specifically, this repository comprises EasyCrypt scripts aimed at the formal verification of certain schemes from the Saber post-quantum cipher suite. 
At present, these scripts cover the formal verification of the desired security and correctness properties of Saber's PKE scheme.

## Repository Structure and Contents
This repository is assembled as follows.
* `SaberPKE/`: All files concerning the formal verification of Saber's PKE scheme.
  * `Deprecated/`: All deprecated files.
  * `MLWRGamesROMSecurity.ec`: Formal verification of the hardness of GMLWR and XMLWR in the ROM.
  * `PolyReduce.ec`: Theory providing structure, definitions, and properties regarding polynomial quotient rings of the form K[X]/X^n + 1.
  * `SaberPKEDeltaCorrectness.ec`: Formal verification of the desired correctness property of Saber's PKE scheme.
  * `SaberPKESecurity.ec`: Formal verification of the desired security property of Saber's PKE scheme.
  * `SaberPKEPreliminaries.ec`: Fundamental preliminaries (e.g., parameters, types, operators) related to Saber's PKE scheme.
