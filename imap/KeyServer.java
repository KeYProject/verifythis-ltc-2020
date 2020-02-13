
public interface KeyServer {

    // @ public instance ghost \locset footprint;

    /*@ instance ghost \map keyStore;
      @ instance ghost \map pendAddEmail;
      @ instance ghost \map pendAddKey;
      @*/

    /*@ public instance invariant (\forall int token;
      @   \dl_inDomain(pendAddEmail, token) == \dl_inDomain(pendAddKey, token));
      @*/
    
    /*@ public normal_behaviour
      @  ensures \result == \dl_inDomain(keyStore, email);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(int email);
    
    /*@ public normal_behaviour
      @  requires \dl_inDomain(keyStore, email);
      @  ensures \result == \dl_mapGet(keyStore, email);
      @  assignable \strictly_nothing;
      @*/
    public int get(int email);

    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures keyStore == \old(keyStore);
      @  ensures pendAddEmail == \dl_mapUpdate(\old(pendAddEmail), \result, id);
      @  ensures pendAddKey == \dl_mapUpdate(\old(pendAddKey), \result, pkey);
      @  // assignable footprint;
      @*/
    public int add(int id, int pkey);
    
    /*@ public normal_behavior
      @  requires \dl_inDomain(pendAddEmail, token);
      @  ensures keyStore == \dl_mapUpdate(\old(keyStore), 
      @     \dl_mapGet(\old(pendAddEmail), token), 
      @     \dl_mapGet(\old(pendAddKey), token));
      @  ensures pendAddEmail == \dl_mapRemove(\old(pendAddEmail), token);
      @  ensures pendAddKey == \dl_mapRemove(\old(pendAddKey), token);
      @  // assignable footprint;
      @*/
    public void addConfirm(int token);
    
}
