# verifythis-ltc-2020 [![Proof Status](https://travis-ci.org/KeYProject/verifythis-lts20.svg?branch=master)](https://travis-ci.org/KeYProject/verifythis-lts20)


This repository gathers the effort of the [KeY team](https://key-project.org)
for the [VerifyThis Collaborative Long-Term Challenge](https://verifythis.github.io/).


Project group: 

* Mattias Ulbrich (@matulbrich)
* Alexander Weigl (@wadoon)



## Verified Software

### A simply email-key map

In [simplified/](simpflified), you find a simple implementation for a email-key
map -- verifiable in KeY. The implementation is based upon two arrays, for the
key and the value. The number of pairs are limited as the arrays are never
resized. It also does not support the verifying part of the *Verifying Key
Server*

### Map version

The next version builds upon the generalization of the previous map structure.
It is currently work in progress.


