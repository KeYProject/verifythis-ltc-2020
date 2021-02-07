public interface KSMap__expanded  {
    //@ public instance ghost \locset footprint;
    
    /*@ public instance model \map mmap; */

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
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void put(String key, String value);

    /*@
      @ public normal_behavior 
      @  ensures mmap == \dl_mapRemove(\old(mmap), key);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void del(String key);

    /*@ public normal_behaviour
      @  ensures \result.mmap == \dl_mapEmpty();
      @  ensures \fresh(\result);
      @  ensures \invariant_for(\result);
      @  assignable \nothing;
      @*/      
    public static KSMap__expanded newMap() {
        return new KSMapImpl();
    }
    
}
