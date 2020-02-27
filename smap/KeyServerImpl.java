public class KeyServerImpl implements KeyServer {

    //@ invariant mapKeys.<inv>;
    private final KSMap mapKeys = KSMap.newMap();

    //@ invariant mapPendAddEmail.<inv>;
    private final KSMap mapPendAddEmail = KSMap.newMap();

    //@ invariant mapPendAddKey.<inv>;
    private final KSMap mapPendAddKey = KSMap.newMap();

    //@ invariant mapPendDelEmail.<inv>;
    private final KSMap mapPendDelEmail = KSMap.newMap();
    
    /*@ invariant mapKeys != mapPendAddEmail && mapKeys != mapPendAddKey &&
      @   mapKeys != mapPendDelEmail && mapPendAddEmail != mapPendAddKey && 
      @   mapPendAddEmail != mapPendDelEmail && mapPendAddKey != mapPendDelEmail;
      @*/

    //@ invariant \dl_isFinite(pendAddEmail);

    //@ invariant keyStore == mapKeys.mmap;
    //@ invariant pendAddEmail == mapPendAddEmail.mmap;
    //@ invariant pendAddKey == mapPendAddKey.mmap;
    //@ invariant pendDelEmail == mapPendDelEmail.mmap;

    /*@ public normal_behaviour
      @  ensures keyStore == \dl_mapEmpty();
      @  ensures pendAddEmail == \dl_mapEmpty();
      @  ensures pendAddKey == \dl_mapEmpty();
      @  // ensures \fresh(footprint);
      @  assignable \nothing;
      @*/
    public KeyServerImpl() {
        //@ set keyStore = \dl_mapEmpty();
        //@ set pendAddEmail = \dl_mapEmpty();
        //@ set pendAddKey = \dl_mapEmpty();
        //@ set pendDelEmail = \dl_mapEmpty();
        // @ set footprint = \everything;
        {}
    }

    public boolean contains(String email) {
        return mapKeys.contains(email);
    }
    
    public String get(String id) {
        return mapKeys.get(id);
    }

    public String add(String id, String pkey) {
        KSMap pAE = mapPendAddEmail;
        KSMap pAK = mapPendAddKey;
        String token = newToken();

        pAE.put(token, id);
                
        pAK.put(token, pkey);

        //@ set pendAddEmail = pAE.mmap;
        //@ set pendAddKey = pAK.mmap;

        return token;
    }


    /*@ public normal_behaviour
      @  ensures !\dl_inDomain(pendAddEmail, \result);
      @  assignable \strictly_nothing;
      @*/
    private String newToken1() {       
        int token = Random.nextInt();
        //@ ghost \map decrDomain = pendAddEmail;
        /*@ loop_invariant (\forall int t; t >= token; \dl_inDomain(pendAddEmail, t) ==> \dl_inDomain(decrDomain, t));
          @ loop_invariant \dl_isFinite(decrDomain);
          @ decreases \dl_mapSize(decrDomain);
          @ assignable \strictly_nothing;
          @*/
        while(mapPendAddEmail.contains("" + token)) {
            //@ set decrDomain = \dl_mapRemove(decrDomain, token);
            token = Random.nextInt();
        }
        return ""+token;
    }
    
    public void addConfirm(String token) {       
        String id = mapPendAddEmail.get(token);
        String pkey = mapPendAddKey.get(token);
        mapPendAddEmail.del(token);
        mapPendAddKey.del(token);
        mapKeys.put(id, pkey);
        
        //@ set pendAddEmail = mapPendAddEmail.mmap;
        //@ set pendAddKey = mapPendAddKey.mmap;
        //@ set keyStore = mapKeys.mmap;

        return;
    }

    public String del(String id) {
        String token = newToken();
        mapPendDelEmail.put(token, id);
         //@ set pendDelEmail = mapPendDelEmail.mmap;
        return token;
    }

    public void delConfirm(String token) {        
        String id = mapPendDelEmail.get(token);
        mapPendDelEmail.del(token);
        mapKeys.del(id);
        
        //@ set pendDelEmail = mapPendDelEmail.mmap;
        //@ set keyStore = mapKeys.mmap;
        return;
    }
}
