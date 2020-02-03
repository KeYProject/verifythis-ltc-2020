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

    // @ invariant unconfirmedDeletionsEmail.<inv>;
    // private final KIMap unconfirmedDeletionsEmail = new KIMapImpl();

    // @ invariant unconfirmedDeletionsKey.<inv>;
    // private final KIMap unconfirmedDeletionsKey = new KIMapImpl();

    /*@ invariant \disjoint(storedKeys.footprint, 
      @  unconfirmedAdditionsEmail.footprint, unconfirmedAdditionsKey.footprint,
      @  //unconfirmedDeletionsEmail.footprint, unconfirmedDeletionsKey.footprint
      @  this.*
      @ );
      @*/

    //@ invariant \dl_isFinite(confAddEmail);

    //@ invariant state == storedKeys.m;
    //@ invariant confAddEmail == unconfirmedAdditionsEmail.m;
    //@ invariant confAddKey == unconfirmedAdditionsKey.m;

    /*@ public normal_behaviour
      @  ensures state == \dl_mapEmpty();
      @  ensures confAddEmail == \dl_mapEmpty();
      @  ensures confAddKey == \dl_mapEmpty();
      @ // ensures \new_elems_fresh(footprint);
      @  assignable \nothing;
      @*/
    public KeyServerImpl() {
        //@ set state = \dl_mapEmpty();
        //@ set confAddEmail = \dl_mapEmpty();
        //@ set confAddKey = \dl_mapEmpty();
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
        // //@ ensures uAE.m == \dl_mapUpdate(\old(confAddEmail), token, id);
        // //@ assignable \strictly_nothing;
        // { int block1; }
        
        uAK.put(token, pkey);

        // //@ normal_behaviour
        // //@ ensures \disjoint(uAE.footprint, uAK.footprint);
        // //@ ensures uAK.m == \dl_mapUpdate(\old(confAddKey), token, pkey);
        // //@ assignable \strictly_nothing;
        // { int block2; }
        
        //@ set confAddEmail = uAE.m;
        //@ set confAddKey = uAK.m;
      
        // KeYInternal.UNFINISHED_PROOF();
        return token;
    }

    /*@ public normal_behaviour
      @  ensures !\dl_inDomain(confAddEmail, \result);
      @  assignable \strictly_nothing;
      @*/
    private int newToken() {       
        int token = Random.nextInt();
        //@ ghost \map decrDomain = confAddEmail;
        /*@ loop_invariant (\forall int t;
          @    t >= token; \dl_inDomain(confAddEmail, t) ==> \dl_inDomain(decrDomain, t));
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
    
    public void addConfirm(int token) {
        if(!unconfirmedAdditionsEmail.contains(token)) {
            return;
        }

        int id = unconfirmedAdditionsEmail.get(token);
        int pkey = unconfirmedAdditionsKey.get(token);
        unconfirmedAdditionsEmail.del(token);
        unconfirmedAdditionsKey.del(token);
        storedKeys.put(id, pkey);
        //@ set state = \dl_mapUpdate(state, id, pkey);
    }    
    
}
