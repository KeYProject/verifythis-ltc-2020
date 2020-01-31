public interface KIMap  {
    //@ public instance ghost \locset footprint;
    
    /*@ public instance ghost \map m; */

    // @ public instance invariant \dl_isIntMap(this.m);
    
    //@ accessible \inv : footprint;

    /*@
      @ public normal_behavior 
      @  ensures \result == \dl_inDomain(m, key);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(int key);
    
    /*@
      @ public normal_behavior 
      @  requires \dl_inDomain(m, key);
      @  ensures \dl_mapGet(m, key) == \result;
      @  assignable \strictly_nothing;
      @*/
    public int get(int key) throws Exception;

    /*@
      @ public normal_behavior 
      @  ensures m == \dl_mapUpdate(\old(m), key, value);
      @  assignable footprint;
      @*/
    public void put(int key, int value);
    

    /*@
      @ public normal_behavior 
      @  ensures m == \dl_mapRemove(\old(m), key);
      @  assignable footprint;
      @*/
    public void del(int key);

}
