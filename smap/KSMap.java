public interface KSMap  {
    //@ private instance ghost \locset footprint;
    /*@ public instance model \map m; */
    //@ accessible m : footprint;
    //@ accessible \inv : footprint;

    /*@
      public normal_behavior 
      ensures \result == \dl_inDomain(m, key);
      assignable \strictly_nothing;
      @*/
    public boolean contains(String key);
    
    /*@
    public normal_behavior 
    requires true; 
    ensures \dl_inDomain(m, key) ==>
                \dl_mapGet(m, key) == \result;
    ensures !\dl_inDomain(m, key) ==> \result == null;
    assignable \strictly_nothing;
    @*/
    public String get(String key);

    /*@
      public normal_behavior 
      ensures \dl_inDomain(m, key);
      ensures \dl_mapGet(m, key) == value;
      ensures m == \dl_mapUpdate(\old(m), key, value);
      //assignable \strictly_nothing;
      assignable footprint;
      @*/
    public void put(String key, String value);
    

    /*@
      public normal_behavior 
      ensures !\dl_inDomain(m, key);
      ensures m == \dl_mapRemove(\old(m), key);
      assignable footprint;
      @*/
    public void del(String key);

}
