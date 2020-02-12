/**
 * This is a simple backend for a verifying KeyServer. 
 *
 * This server uses integer values for the token, email and keys.
 * 
 * @author Alexander Weigl <weigl@kit.edu>
 * @version 1, 2019-12-10
 */
public class KeyServerImpl implements KeyServer {

    //@ invariant storedKeys.<inv>;
    private final KIMap storedKeys = new KIMapImpl();

    //@ invariant unconfirmedAdditionsEmail.<inv>;
    private final KIMap unconfirmedAdditionsEmail = new KIMapImpl();

    //@ invariant unconfirmedAdditionsKey.<inv>;
    private final KIMap unconfirmedAdditionsKey = new KIMapImpl();

    //@ invariant unconfirmedDeletionsEmail.<inv>;
    private final KIMap unconfirmedDeletionsEmail = new KIMapImpl();

    //@ invariant unconfirmedDeletionsKey.<inv>;
    private final KIMap unconfirmedDeletionsKey = new KIMapImpl();

    /*@ invariant \disjoint(storedKeys.footprint, 
      @  unconfirmedAdditionsEmail.footprint, unconfirmedAdditionsKey.footprint,
      @  //unconfirmedDeletionsEmail.footprint, unconfirmedDeletionsKey.footprint
      @  this.*
      @ );
      @*/

    // HACK ONLY
    /*@ model_behaviour 
      @  signals (Throwable ex) false;
      @  ensures \result == x.mmap; 
      @ model helper instance \map mmmap(KIMap x) { return x.mmap; }
      @*/

    //@ invariant \dl_isFinite(pendAddEmail);

    //@ invariant database == storedKeys.mmap;
    //@ invariant pendAddEmail == unconfirmedAdditionsEmail.mmap;
    //@ invariant pendAddKey == unconfirmedAdditionsKey.mmap;

    /*@ public normal_behaviour
      @  ensures database == \dl_mapEmpty();
      @  ensures pendAddEmail == \dl_mapEmpty();
      @  ensures pendAddKey == \dl_mapEmpty();
      @ // ensures \new_elems_fresh(footprint);
      @  assignable \nothing;
      @*/
    public KeyServerImpl() {
        //@ set database = \dl_mapEmpty();
        //@ set pendAddEmail = \dl_mapEmpty();
        //@ set pendAddKey = \dl_mapEmpty();
        // @ set footprint = \everything;
        {}
    }

    public boolean contains(int email) {
        return storedKeys.contains(email);
    }
    
    public int get(int id) {
        return storedKeys.get(id);
    }

    public int add(int id, int pkey) {
        // KeYInternal.UNFINISHED_PROOF();
        KIMap uAE = unconfirmedAdditionsEmail;
        KIMap uAK = unconfirmedAdditionsKey;
        int token = newToken();
        uAE.put(token, id);
        
        // //@ normal_behaviour
        // //@ ensures \disjoint(uAE.footprint, uAK.footprint);
        // //@ ensures uAE.mmap == \dl_mapUpdate(\old(pendAddEmail), token, id);
        // //@ assignable \strictly_nothing;
        // { int block1; }
        
        uAK.put(token, pkey);

        // //@ normal_behaviour
        // //@ ensures \disjoint(uAE.footprint, uAK.footprint);
        // //@ ensures uAK.mmap == \dl_mapUpdate(\old(pendAddKey), token, pkey);
        // //@ assignable \strictly_nothing;
        // { int block2; }

        // HACK. Should be "pendAddEmail = uAE.mmap;"
        //@ set pendAddEmail = mmmap(uAE);
        //@ set pendAddKey = mmmap(uAK);
        ;
      
        // KeYInternal.UNFINISHED_PROOF();
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
        while(unconfirmedAdditionsEmail.contains(token)) {
            //@ set decrDomain = \dl_mapRemove(decrDomain, token);
            token++;
            {}
        }
        return token;
    }
    
    public void addConfirm(int tokenNumber) {
        KeYInternal.UNFINISHED_PROOF();
        int id = unconfirmedAdditionsEmail.get(tokenNumber);
        unconfirmedAdditionsEmail.del(tokenNumber);
        int pkey = unconfirmedAdditionsKey.get(tokenNumber);
        unconfirmedAdditionsKey.del(tokenNumber);
        storedKeys.put(id, pkey);
    }

    public int del(int id) {      
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

    public void delConfirm(int token) {
      KeYInternal.UNFINISHED_PROOF();
      KIMap uDE = unconfirmedDeletionsEmail;
      KIMap uDK = unconfirmedDeletionsKey;

      int id = uDE.get(tokenNumber);
      int pkey = uDK.get(tokenNumber);

      uDE.del(tokenNumber);
      uDK.del(tokenNumber);

      if(storedKeys.get(id) == pkey) {}
        storedKeys.del(id);
      }
    }
    
}
