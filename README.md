# Formal Verification of Saber's Public-Key Encryption Scheme in EasyCrypt
This repository accompanies the paper "Formal Verification of Saber's Public-Key Encryption Scheme in EasyCrypt", authored by Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub. The original (proceeding's) version of the paper can be found [here](https://doi.org/10.1007/978-3-031-15802-5_22); the extended and updated version of the paper can be found [here](https://eprint.iacr.org/2022/351).\
\
This repository comprises EasyCrypt scripts aimed at the formal verification of the public-key encryption (PKE) scheme from the [Saber post-quantum cipher suite](https://www.esat.kuleuven.be/cosic/pqcrypto/saber/). 
More precisely, these scripts cover the formal verification of the IND-CPA security and delta-correctness properties of Saber's PKE scheme.\
\
The version of EasyCrypt used to construct the scripts in this repository corresponds to the following commit (of the main branch) of the [EasyCrypt repository](https://github.com/EasyCrypt/easycrypt): `commit r2022.04-63-gbe402987`

## Repository Structure and Contents
This repository is structured as follows.
* `saberpke/`: All files concerning the formal verification of Saber's PKE scheme.
  * `MLWRGamesROMSecurity.ec`: Formal verification of the hardness of GMLWR and XMLWR in the ROM.
  * `PolyReduce.ec`: Theory providing structure, definitions, and properties regarding polynomial quotient rings of the form K[X]/X^n + 1.
  * `SaberPKEDeltaCorrectness.ec`: Formal verification of the desired correctness property of Saber's PKE scheme.
  * `SaberPKEPreliminaries.ec`: Fundamental preliminaries (e.g., parameters, types, operators) related to Saber's PKE scheme.
  * `SaberPKESecurity.ec`: Formal verification of the desired security property of Saber's PKE scheme.
