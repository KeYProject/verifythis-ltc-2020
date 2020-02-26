
public interface KeyServer {

    // @ public instance ghost \locset footprint;

    /*@ instance ghost \map keyStore;
      @ instance ghost \map pendAddEmail;
      @ instance ghost \map pendAddKey;
      @ instance ghost \map pendDelEmail;
      @*/

    /*@ public instance invariant (\forall int token;
      @   \dl_inDomain(pendAddEmail, token) == \dl_inDomain(pendAddKey, token));
      @*/
    
    /*@ public normal_behaviour
      @  ensures \result == \dl_inDomain(keyStore, email);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(String email);
    
    /*@ public normal_behaviour
      @  requires \dl_inDomain(keyStore, email);
      @  ensures \result == \dl_mapGet(keyStore, email);
      @  assignable \strictly_nothing;
      @*/
    public String get(String email);
    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures keyStore == \old(keyStore);
      @  ensures pendAddEmail == \dl_mapUpdate(\old(pendAddEmail), \result, id);
      @  ensures pendAddKey == \dl_mapUpdate(\old(pendAddKey), \result, pkey);
      @  ensures pendDelEmail == \old(pendDelEmail);
      @  ensures !\dl_inDomain(\old(pendAddEmail), \result);
      @  // assignable footprint;
      @*/
    public String add(String id, String pkey);
    
    /*@ public normal_behavior
      @  requires \dl_inDomain(pendAddEmail, token);
      @  ensures keyStore == \dl_mapUpdate(\old(keyStore), 
      @     \dl_mapGet(\old(pendAddEmail), token), 
      @     \dl_mapGet(\old(pendAddKey), token));
      @  ensures pendAddEmail == \dl_mapRemove(\old(pendAddEmail), token);
      @  ensures pendAddKey == \dl_mapRemove(\old(pendAddKey), token);
      @  ensures pendDelEmail == \old(pendDelEmail);
      @  // assignable footprint;
      @*/
    public void addConfirm(String token);
   
    /*@ public normal_behaviour
      @  ensures keyStore == \old(keyStore);
      @  ensures pendAddEmail == \old(pendAddEmail);
      @  ensures pendAddKey == \old(pendAddKey);
      @  ensures pendDelEmail == \dl_mapUpdate(\old(pendDelEmail), \result, id);
      @  ensures !\dl_inDomain(\old(pendAddEmail), \result);
      @  // assignable footprint;
      @*/
    public String del(String id);

    /*@ public normal_behavior
      @  requires \dl_inDomain(pendDelEmail, token);
      @  ensures keyStore == \dl_mapRemove(\old(keyStore),
      @     \dl_mapGet(\old(pendDelEmail), token));
      @  ensures pendAddEmail == \old(pendAddEmail);
      @  ensures pendAddKey == \old(pendAddKey);
      @  ensures pendDelEmail == \dl_mapRemove(\old(pendDelEmail), token);
      @  // assignable footprint;
      @*/
    public void delConfirm(String token);

    
    
}
