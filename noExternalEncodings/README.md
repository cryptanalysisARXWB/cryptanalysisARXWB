Demonstration code for the attacks where either the input/output external encoding is trivial.

The `white_box_backend.c` file is a pre-generated instance of Whitebox'd Speck32 without external encodings, generated using the authors' implementation.

The `white_box_arx.c` file is a sligthly modified version of the same file provided by the authors to provide additional functionalities like easily making a query to a specific round function.

This is all handled in Sage/Python with the `simplifiedOracle.py` module, which essentially just compile a shared library using the `white_box_backend.c` data for the whitebox instance, and allows for (relatively) fast queries to the oracle from Sage/Python code.

The attacks are given in `algebraicAttackNoInputEE.py` and `algebraicAttackNoOutputEE.py`.
Both can be executed simply with `sage algebraicAttackNoInputEE.py` (or `sage algebraicAttackNoOutputEE.py` respectively).

Note that the authors' implementation does not provide an easy way to disable only the input/output encoding. Thus the pre-computed instance given in `white_box_backend.c` does not have neither the input nor output external encoding.
In practice, this has no impact on our code, as the attack without *output* external encoding only use queries to the 5 last rounds to recover the masterkey, thus the input external encoding has no effect anyway since it's only involved in the first round.
Similarly, the attack without *input* external encoding only use queries to the 6 first rounds to recover the masterkey, thus the output external encoding has no effect in this case.

## Prerequisites

Requires a C compiler, SageMath and installed M4RI ( https://bitbucket.org/malb/m4ri , required to run the white-box implementation ).