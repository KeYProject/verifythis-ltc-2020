/**
 * This is a simple backend for a verifying KeyServer. 
 *
 * This server uses integer values for the token, email and keys.
 * 
 * @author Alexander Weigl <weigl@kit.edu>
 * @version 1, 2019-12-10
 */
public class KeyServerImpl implements KeyServer {

    //@ invariant mapKeys.<inv>;
    private final KIMap mapKeys = KIMap.newMap();

    //@ invariant mapPendAddEmail.<inv>;
    private final KIMap mapPendAddEmail = KIMap.newMap();

    //@ invariant mapPendAddKey.<inv>;
    private final KIMap mapPendAddKey = KIMap.newMap();

    //@ invariant unconfirmedDeletionsEmail.<inv>;
    private final KIMap unconfirmedDeletionsEmail = KIMap.newMap();

    //@ invariant unconfirmedDeletionsKey.<inv>;
    private final KIMap unconfirmedDeletionsKey = KIMap.newMap();

    /*@ invariant mapKeys != mapPendAddEmail && mapKeys != mapPendAddKey &&
      @   mapPendAddEmail != mapPendAddKey && mapPendAddEmail != mapPendDelKey 
      @   mapPendAddKey != mapPendDelKey && mapPendDelKey != mapPendDelEmail;
      @*/

    //@ invariant \dl_isFinite(pendAddEmail);
    //@ invariant \dl_isFinite(pendDelEmail);

    //@ invariant keyStore == mapKeys.mmap;
    //@ invariant pendAddEmail == mapPendAddEmail.mmap;
    //@ invariant pendAddKey == mapPendAddKey.mmap;
    //@ invariant pendDelEmail == mapPendDelEmail.mmap;
    //@ invariant pendDelKey == mapPendDelKey.mmap;

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
        // @ set footprint = \everything;
        {}
    }

    public boolean contains(int email) {
        return mapKeys.contains(email);
    }
    
    public int get(int id) {
        return mapKeys.get(id);
    }

    public int add(int id, int pkey) {
        // KeYInternal.UNFINISHED_PROOF();
        KIMap pAE = mapPendAddEmail;
        KIMap pAK = mapPendAddKey;
        int token = newToken();        

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
    private int newToken() {       
        int token = Random.nextInt();
        //@ ghost \map decrDomain = pendAddEmail;
        /*@ loop_invariant (\forall int t;
          @    t >= token; \dl_inDomain(pendAddEmail, t) ==> \dl_inDomain(decrDomain, t));
          @ loop_invariant \dl_isFinite(decrDomain);
          @  decreases \dl_mapSize(decrDomain);
          @  assignable \strictly_nothing;
          @*/
        while(mapPendAddEmail.contains(token)) {
            //@ set decrDomain = \dl_mapRemove(decrDomain, token);
            token++;
            {}
        }
        return token;
    }
    
    public void addConfirm(int tokenNumber) {
        KeYInternal.UNFINISHED_PROOF();
        int id = mapPendAddEmail.get(tokenNumber);
        mapPendAddEmail.del(tokenNumber);
        int pkey = mapPendAddKey.get(tokenNumber);
        mapPendAddKey.del(tokenNumber);
        mapKeys.put(id, pkey);
    }    
    
  public int del(int id) {    
        KeYInternal.UNFINISHED_PROOF();  
        KIMap uDE = unconfirmedDeletionsEmail;
        KIMap uDK = unconfirmedDeletionsKey;
        int pkey = get(id);
        int token = newToken();
        uDE.put(token, id);              
        uDK.put(token, pkey);

        // HACK. Should be "pendAddEmail = uAE.mmap;"
        //@ set pendDelEmail = mmmap(uDE);
        //@ set pendDelKey = mmmap(uDK);
        ;
        return token;
    }

    public void delConfirm(int tokenNumber) {
      KeYInternal.UNFINISHED_PROOF();
      KIMap uDE = unconfirmedDeletionsEmail;
      KIMap uDK = unconfirmedDeletionsKey;

      int id = uDE.get(tokenNumber);
      int pkey = uDK.get(tokenNumber);

      uDE.del(tokenNumber);
      uDK.del(tokenNumber);

      if(mapKeys.get(id) == pkey) {
        mapKeys.del(id);
      }
    }
}
