public interface KSMap  {
    //@ public instance ghost \free footprint;
    
    //@ public instance model \map mmap;
    //@  accessible mmap : footprint;
   
    //@ accessible \inv : footprint;

    /*@
      @ public normal_behavior 
      @  ensures \result == \dl_inDomain(mmap, key);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(String key);
    
    /*@
      @ public normal_behavior 
      @  requires \dl_inDomain(mmap, key);
      @  ensures \dl_mapGet(mmap, key) == \result;
      @  assignable \strictly_nothing;
      @*/
    public String get(String key);

    /*@
      @ public normal_behavior 
      @  ensures mmap == \dl_mapUpdate(\old(mmap), key, value);
      @  assignable footprint;
      @*/
    public void put(String key, String value);

    /*@
      @ public normal_behavior 
      @  ensures mmap == \dl_mapRemove(\old(mmap), key);
      @  assignable footprint;
      @*/
    public void del(String key);


    /*@ public normal_behaviour
      @  ensures \result.mmap == \dl_mapEmpty();
      @  ensures \fresh(\result);
      @  ensures \invariant_for(\result);
      @  assignable \nothing;
      @*/      
    public static KSMap newMap() {
        // It is a marker function only.
        KeYInternal.UNFINISHED_PROOF();
        throw new Error();
    }
    

}
