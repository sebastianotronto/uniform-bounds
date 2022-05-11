# Some uniform bounds for elliptic curves over Q

This repository contains the [MAGMA](http://magma.maths.usyd.edu.au/magma)
cited in the paper *Some uniform bounds for elliptic curves
over Q* by Davide Lombardo and Sebastiano Tronto (available on
[arXiv](https://arxiv.org/abs/2106.09950), submitted for publication to
the Pacific Journal of Mathematics).

## Files

The files Examples2.m and ExamplesOdd.m verify the contents of Tables
1 and 2 in Section 7. The file Theorem44.m verifies several claims made
in the proof of Theorem 4.4.

Note that Theorem44.m is based on the classification by Rouse and
Zureick-Brown of all possible 2-adic images of Galois for non-CM elliptic
curves over Q. As such, running it requires the following 4 data files:
* gl2finedata.txt
* gl2data.txt
* curvelist1.txt
* curvelist2.txt
which may be obtained from
[J. Rouse's page](https://users.wfu.edu/rouseja/2adic).

Output files for all the scripts are also provided.
