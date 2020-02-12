
public interface KeyServer {

    // @ public instance ghost \locset footprint;

    /*@ instance ghost \map database;       
      @ instance ghost \map pendAddEmail;
      @ instance ghost \map pendAddKey;
      @ instance ghost \map pendDelEmail;
      @ instance ghost \map pendDelKey;
      @*/

    /*@ instance invariant (\forall int token;
      @   \dl_inDomain(pendAddEmail, token) == \dl_inDomain(pendAddKey, token));
      @*/
    
    /*@ public normal_behaviour
      @  ensures \result == \dl_inDomain(database, email);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(int email);
    
    /*@ public normal_behaviour
      @  requires \dl_inDomain(database, email);
      @  ensures \result == \dl_mapGet(database, email);
      @  assignable \strictly_nothing;
      @*/
    public int get(int email);

    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures database == \old(database);
      @  ensures pendAddEmail == \dl_mapUpdate(\old(pendAddEmail), \result, id);
      @  ensures pendAddKey == \dl_mapUpdate(\old(pendAddKey), \result, pkey);
      @  // assignable footprint;
      @*/
    public int add(int id, int pkey);
    
    /*@ public normal_behavior
      @  requires \dl_inDomain(pendAddEmail, token);
      @  ensures database == \dl_mapUpdate(\old(database), 
      @     \dl_mapGet(pendAddEmail, token), \dl_mapGet(pendAddKey, token));
      @  ensures pendAddEmail == \dl_mapRemove(\old(pendAddEmail), token);
      @  ensures pendAddKey == \dl_mapRemove(\old(pendAddKey), token);
      @  // assignable footprint;
      @*/
    public void addConfirm(int token);
    
}
