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

    //@ invariant mapPendDelEmail.<inv>;
    private final KIMap mapPendDelEmail = KIMap.newMap();
    
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

    public boolean contains(int email) {
        return mapKeys.contains(email);
    }
    
    public int get(int id) {
        return mapKeys.get(id);
    }

    public int add(int id, int pkey) {
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
        }
        return token;
    }
    
    public void addConfirm(int token) {       
        int id = mapPendAddEmail.get(token);
        int pkey = mapPendAddKey.get(token);
        mapPendAddEmail.del(token);
        mapPendAddKey.del(token);
        mapKeys.put(id, pkey);
        
        //@ set pendAddEmail = mapPendAddEmail.mmap;
        //@ set pendAddKey = mapPendAddKey.mmap;
        //@ set keyStore = mapKeys.mmap;

        return;
    }

    public int del(int id) {
        int token = newToken();
        mapPendDelEmail.put(token, id);
         //@ set pendDelEmail = mapPendDelEmail.mmap;
        return token;
    }

    public void delConfirm(int token) {
        
        int id = mapPendDelEmail.get(token);
        mapPendDelEmail.del(token);
        mapKeys.del(id);
        
        //@ set pendDelEmail = mapPendDelEmail.mmap;
        //@ set keyStore = mapKeys.mmap;

        return;
    }
}
