
public interface KeyServer {

    // @ public instance ghost \locset footprint;

    /*@ instance ghost \map state;
      @ instance ghost \map confAddEmail;
      @ instance ghost \map confAddKey;
      @*/

    /*@ public instance invariant (\forall int token;
      @   \dl_inDomain(confAddEmail, token) == \dl_inDomain(confAddKey, token));
      @*/
    
    /*@ public normal_behaviour
      @  ensures \result == \dl_inDomain(state, email);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(int email);
    
    /*@ public normal_behaviour
      @  requires \dl_inDomain(state, email);
      @  ensures \result == \dl_mapGet(state, email);
      @  assignable \strictly_nothing;
      @*/
    public int get(int email);

    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures state == \old(state);
      @  ensures confAddEmail == \dl_mapUpdate(\old(confAddEmail), \result, id);
      @  ensures confAddKey == \dl_mapUpdate(\old(confAddKey), \result, pkey);
      @  // assignable footprint;
      @*/
    public int add(int id, int pkey);
    
    /*@ public normal_behavior
      @  requires \dl_inDomain(confAddEmail, token);
      @  ensures state == \dl_mapUpdate(\old(state), 
      @     \dl_mapGet(confAddEmail, token), \dl_mapGet(confAddKey, token));
      @  ensures confAddEmail == \dl_mapRemove(\old(confAddEmail), token);
      @  ensures confAddKey == \dl_mapRemove(\old(confAddKey), token);
      @  // assignable footprint;
      @
      @ also 
      @ public normal_behavior
      @  requires !\dl_inDomain(confAddEmail, token);
      @  assignable \strictly_nothing;
      @*/
    public void addConfirm(int token);
    
}
