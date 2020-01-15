# KeY-key-server

Currently, due to additional modelling `project.key` must be loaded.
There are additional symbols and rules.

## The keyserver

* Uses the map interfaces.
* Issues confirmation codes.

## The map interface

* Alternatives: `\map` data type or using pure functions and specify
  via them.
  
* Implementation with two arrays is there. Specification is there.

* Verification is on its way.

### Challenges

* Map takes `any` as key; this data type is not available in JML. So
  we cannot specify that all keys are integers.  Hence, I created a
  predicate `isIntMap` that is true if all keys and values in a map
  are integer values.
  
* [ ] There is still a flaw in that definition. It should be
      `!x. inDomain(m, x) -> int:instance(get(m, x))=TRUE`

* Implementation seems to be very difficult. Lots of interaction seems
  to be needed.
