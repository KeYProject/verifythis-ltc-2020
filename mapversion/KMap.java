public class KMap  {
    /*@ public model \map m; */

    //@ invariant m != null;

    /*@
    ensures \result != null <==> \dl_inDomain(m, key);
    
    @*/
    public Object get(Object key)
    {}

    /*@
      ensures \dl_inDomain(m, key);
      ensures \dl_mapGet(m, key) == value;
      ensures m == \dl_mapUpdate(m, key, value);
      @*/
    public void put(Object key, Object value)
    {}

    /*@
      ensures !\dl_inDomain(m, key);
      ensures m == \dl_mapRemove(m, key);
      @*/
    public void del(Object key)     {}

}
