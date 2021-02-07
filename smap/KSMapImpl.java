public class KSMapImpl implements KSMap__expanded  {

    private int count;

    private String[] keys;
    private String[] values;

    //@ ghost \map gmap;

    //@ represents mmap = gmap;

    //@ invariant keys.length > 0;
    //@ invariant keys.length == values.length;
    //@ invariant keys != values;
    //@ invariant 0 <= count && count <= keys.length;
    //@ invariant (\forall int i,j; 0 <= i && i < j && j < count; keys[i] != keys[j]);
    //@ invariant (\forall int i,j; 0 <= i && i < count && 0<=j && j < count; keys[i] != values[j]);
    //@ invariant (\forall int i; 0 <= i && i < count; keys[i] != null && values[i]!=null);
    

    /*@ invariant (\forall String x; 
      @                \dl_inDomain(gmap, x) 
      @           <==> (\exists int j; 0<=j && j<count; keys[j] == x));
      @ invariant (\forall int j;  0 <= j && j < count;
      @             \dl_mapGet(gmap, keys[j]) == values[j]);
      @*/
    
    /*@ invariant footprint == \set_union(
      @    \all_fields(this), \set_union(
      @    \all_fields(values), \all_fields(keys)));
      @*/

    // @  ensures footprint ==  \set_union(
    // @        \all_fields(this), \set_union(
    // @        \all_fields(values), \all_fields(keys)));
    
    /*@ public normal_behaviour
      @  ensures mmap == \dl_mapEmpty();
      @  ensures \fresh(footprint);
      @  assignable \nothing;
      @*/
    public KSMapImpl() {
        this.count = 0;
        this.keys = new String[1024];
        this.values = new String[1024];
        //@ set gmap = \dl_mapEmpty();
        /*@ set footprint = \set_union(
              \all_fields(this), \set_union(
              \all_fields(values), \all_fields(keys)));
        */
        {}
    }

    /*@ normal_behavior
      @  requires newSize >= array.length;
      @  requires 0 <= count && count <= array.length;
      @  ensures \fresh(result);
      @  ensures (\forall int i; 0 <= i && i < count; \result[i] == array[i]);
      @  ensures \result.length == newSize;
      @  assignable \nothing;
      @  helper
      @*/
    private String[] arrayClone(String[] array, int newSize) {
      String[] newArray = new String[newSize];
        /*@ loop_invariant 0 <= i && i <= count;
          @ loop_invariant (\forall int j; 0 <= j && j < i;
          @   newArray[j] == array[j]);
          @ loop_invariant (newArray != array);
          @ assignable newArray[*];
          @ decreases array.length - i;
          @*/
        for(int i = 0; i < count; i++) {
            newArray[i] = array[i];
        }
        return newArray;
    }

    /*@ normal_behavior 
      @  requires newSize >= keys.length;
      @  ensures  keys.length == newSize;
      @  ensures  values.length == newSize;
      @  ensures  (\forall int i; 0 <= i && i < count;
      @             keys[i] == \old(keys[i]) && values[i] == \old(values[i]));
      @  ensures \fresh(keys) && \fresh(values);
      @  assignable values, keys, \singleton(footprint);
     */
    private void resize(int newSize) {
      String[] newkeys = arrayClone(keys, newSize);
      String[] newvalues = arrayClone(values, newSize);

        this.keys = newkeys;
        this.values = newvalues;

        //@ set footprint = \set_union(\all_fields(this), \set_union(\all_fields(values), \all_fields(keys)));
    }
          
    /*@ normal_behaviour 
      @  requires true;
      @  ensures \result >= -1;
      @  ensures \result < 0 ==> (\forall int i; 0 <= i && i < count; !keys[i].equals(id));
      @  ensures \result >= 0 ==> (keys[\result].equals(id) && \result < count);
      @  assignable \strictly_nothing; 
      @*/    
    private int posOfId(String id) {
        /*@ loop_invariant (\forall int k; 0 <= k && k < i; !keys[k].equals(id));
          @ loop_invariant 0 <= i && i <= count;
          @ 
          @ decreases keys.length - i; 
          @ assignable \strictly_nothing;
          @*/
        for(int i = 0; i < count;  i++) {
            if(keys[i].equals(id)) {
                return i;
            }            
        }
        return -1;
    }   


    /*@
      @ public normal_behavior 
      @  ensures \result == (\exists int i; 0 <= i && i < count; keys[i].equals(key));
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(String key) {
        int pos = posOfId(key);
        return pos >= 0;
    }

    
    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; keys[i].equals(id));
      @  ensures (\exists int i; 0 <= i && i < count; \result.equals(values[i]) && keys[i].equals(id));
      @  assignable \strictly_nothing;
      @
      @ also public exceptional_behavior       
      @  requires (\forall int i; 0 <= i && i < count; !keys[i].equals(id)); 
      @  signals (IllegalArgumentException e) true;
      @  assignable \nothing;
      @*/
    public String get(String id) {
        int pos = posOfId(id);
        if(pos >= 0) 
            return values[pos];
        else 
            throw new IllegalArgumentException();       
    }

  
    /*@ public normal_behaviour
      @  requires count <= keys.length - 1;
      @  ensures 0 <= \result;
      @  ensures count == \old(count) && \result < count
      @      ||  count == \old(count) + 1 && \result == count - 1;
      @  ensures keys[\result].equals(id) && values[\result].equals(pkey);
      @  // preservation of the remaining entries
      @  ensures gmap == \dl_mapUpdate(\old(gmap), id, pkey);
      @  assignable keys[*], values[*], count, gmap;
      @*/
    private int add(String id, String pkey) {
        int pos = posOfId(id);
        
        if(pos < 0) {
            pos = count;
            count ++;
        }
                
        keys[pos] = id;
        values[pos] = pkey;

        //@ set gmap = \dl_mapUpdate(gmap, id, pkey);
        
        return pos;
    }

    public void put(String key, String value) {
        if(count == keys.length) {
            resize(keys.length*2);
        }
        add(key, value);
    }
    
    public void del(String id) {
        int pos = posOfId(id);
        if(pos >= 0) {
            count --;
            if(count > 0 && pos != count) {
                keys[pos] = keys[count];
                values[pos] = values[count];
            }
            
            //@ set gmap = \dl_mapRemove(gmap, id);
            {}
        }        
    }
}
