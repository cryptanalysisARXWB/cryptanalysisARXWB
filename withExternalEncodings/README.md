# Key recovery attack (with both external encodings)

Demonstration code for the attack *with* both external (input and output) encodings).

The `white_box_backend.c` file is a pre-generated instance of Whitebox'd Speck32 with both external encodings, generated using the authors' implementation.

The `white_box_arx.c` file is a sligthly modified version of the same file provided by the authors to provide additional functionalities like easily making a query to a specific round function.

This is all handled in Sage/Python with the `simplifiedOracle.py` module, which essentially just compile a shared library using the `white_box_backend.c` data for the whitebox instance, and allows for (relatively) fast queries to the oracle from Sage/Python code.

**Note:** due to size constraints, we do not upload a Speck64 white-box implementation. It can be generated using the white-box arx framework ( https://github.com/ranea/whiteboxarx ). The attack script applies directly to Speck64, only the `n` parameter needs to be changed from 16 to 32.


## Prerequisites

Requires a C compiler, SageMath and the following python libraries inside the sage environment, and installed M4RI ( https://bitbucket.org/malb/m4ri , required to run the white-box implementation ):

```sh
sage -pip install -U tqdm binteger
```

Also, need to compile the fast bilinear optimization library:

```sh
make
```


## Running the attack

The decomposition + key recovery attack can be ran as follows:

```sh
sage key_recovery_attack.py
```

The script [./key_recovery_attack.py](./key_recovery_attack.py) is the main file. It can be be modified to attack Speck64 by setting `n=32`. Similarly, the number of rounds can be changed (decompose all rounds or 8 to recover just a few master key candidates).

An output log of a successful run can be found in [./key_recovery_attack.log](./key_recovery_attack.log).

**Note:** the script caches intermediate decompositions, please clear the cache folder if you want to start from scratch.