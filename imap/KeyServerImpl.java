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
      @  unconfirmedAdditionsEmail.footprint, unconfirmedAdditionsKey.footprint
      @  //unconfirmedDeletionsEmail.footprint, unconfirmedDeletionsKey.footprint
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
        KeYInternal.UNFINISHED_PROOF();
        int token = newToken();
        unconfirmedAdditionsEmail.put(token, id);
        unconfirmedAdditionsKey.put(token, pkey);
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
    
    public void addConfirm(int tokenNumber) {
        KeYInternal.UNFINISHED_PROOF();
        int id = unconfirmedAdditionsEmail.get(tokenNumber);
        unconfirmedAdditionsEmail.del(tokenNumber);
        int pkey = unconfirmedAdditionsKey.get(tokenNumber);
        unconfirmedAdditionsKey.del(tokenNumber);
        storedKeys.put(id, pkey);
    }    
    
}
