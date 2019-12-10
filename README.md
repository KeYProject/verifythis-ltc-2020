# verifythis-ltc-2020 [![Proof Status](https://travis-ci.org/KeYProject/verifythis-ltc-2020.svg?branch=master)](https://travis-ci.org/KeYProject/verifythis-ltc-2020)


This repository gathers the effort of the [KeY team](https://key-project.org)
for the [VerifyThis Collaborative Long-Term Challenge](https://verifythis.github.io/).


Project group: 

* Mattias Ulbrich (@matulbrich)
* Alexander Weigl (@wadoon)


**Note:** The distributed `key-2.7-exe.jar` is licensed under GPLv2+. The license of the remaining Java sources are not determined yet.

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

* KIMap (*K*ey *I*nteger Map) is an interface representing a map of `Int -> Int`. This functionality is bound to the behaviour of the map data type in KeY by JML specification.
* KIMapImpl is a simple implementation based upon two int arrays, one for the key, the other the values.


