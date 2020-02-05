# verifythis-ltc-2020 [![Proof Status](https://travis-ci.org/KeYProject/verifythis-ltc-2020.svg?branch=master)](https://travis-ci.org/KeYProject/verifythis-ltc-2020)


This repository gathers the effort of the [KeY team](https://key-project.org)
for the [VerifyThis Collaborative Long-Term Challenge](https://verifythis.github.io/).


Project group: 

* Stijn de Gouw
* Mattias Ulbrich (@matulbrich)
* Alexander Weigl (@wadoon)


**Note:** The distributed `key-2.7-exe.jar` is licensed under GPLv2+. The license of the remaining Java sources are not determined yet.

## Verified Software

### A simply email-key map

In [simplified/](simpflified), you find a simple implementation for the keyserver
-- verifiable without interactions in KeY. The implementation is based upon
four integer arrays which store
* the id/email of the user, represented currently by an integer
* two arrays for confirmed and unconfirmed keys, and
* an array that stores confirmation codes.
The number of users is limited, as the arrays are never resized.

### Map version

The next version builds upon the generalization of the previous map structure.
It is currently work in progress. This is a two-step process. The first step is
a provable version using maps of `int` to `int`. This avoids working with the
heap. 

* KIMap (*K*ey *I*nteger Map) is an interface representing a map of `Int ->
  Int`. This functionality is bound to the behaviour of the map data type in KeY
  by JML specification.
* KIMapImpl is a simple implementation based upon two int arrays, one for the
  key, the other the values.
* `KeyServerInt` is a version of the backend of the verifying key server using
  integers as e-mail addresses and keys.

The second step is to use Strings. This results into `KSMap` and `KSMapImpl` and
also the `KeyServerString`.
