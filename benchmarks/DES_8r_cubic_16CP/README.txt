DES_8r_cubic_16CP.anf is the original file.
DES_8b.anf is a lightly modified version, some simple replacements (sed of "s/=/+", "s/+0//", "/\// d") to help get it into the right format for CNF conversion.
DES_8c.anf is after running a simple Python script (anfToanf2cnf.py) that converts DES_8b.anf into the format accepted by anf2cnf.
DES_8.cnf is the result after running anf2cnf --xor on DES_8c.anf.
DES_8_noxor.cnf is too large to be included in the repository (400 mb). It can be recreated by running the xor_to_cnf tool from the cnf-utils package on DES_8.cnf.
