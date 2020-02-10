public interface KIMap__expanded  {
    //@ public instance ghost \locset footprint;
    
    /*@ public instance model \map mmap; */

    //@ accessible \inv : footprint;

    /*@
      @ public normal_behavior 
      @  ensures \result == \dl_inDomain(mmap, key);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(int key);
    
    /*@
      @ public normal_behavior 
      @  requires \dl_inDomain(mmap, key);
      @  ensures \dl_mapGet(mmap, key) == \result;
      @  assignable \strictly_nothing;
      @*/
    public int get(int key);

    /*@
      @ public normal_behavior 
      @  ensures mmap == \dl_mapUpdate(\old(mmap), key, value);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void put(int key, int value);

    /*@
      @ public normal_behavior 
      @  ensures mmap == \dl_mapRemove(\old(mmap), key);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void del(int key);

}
