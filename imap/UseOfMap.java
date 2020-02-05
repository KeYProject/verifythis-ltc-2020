// class UseOfMap {

//     /*@
//       requires map != null;
//       requires map.<inv>;
//       ensures map.get(0) == 0;
//       //assignables m;
//       @*/
//     public KIMap initialize(KIMap map) {
//         map.put(0,0);
//         return map;
//     }

//     /*@
//       requires ignore.<inv>;
//       requires target.<inv>;
//       requires \disjoint(ignore.footprint, target.footprint);
//       ensures target.get(0) == 0;
//       ensures ignore.get(0) == \old(ignore.get(0));
//       @*/
//     public void initialize(KIMap target, KIMap ignore) {
//         target.put(0,0);
//     }


// }

