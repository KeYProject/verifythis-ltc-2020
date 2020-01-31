public class KIMapImpl implements KIMap  {

    private int count;

    private int[] keys;
    private int[] values;

    //@ invariant keys.length > 0;
    //@ invariant keys.length == values.length;
    //@ invariant keys != values;
    //@ invariant 0 <= count && count <= keys.length;
    //@ invariant (\forall int i,j; 0 <= i && i < j && j < count; keys[i] != keys[j]);

    /*@ invariant (\forall int x; 
      @                \dl_inDomain(m, x) 
      @           <==> (\exists int j; 0<=j && j<count; keys[j] == x));
      @ invariant (\forall int j;  0 <= j && j < count;
      @             \dl_mapGet(m, keys[j]) == values[j]);
      @*/
    
    /*@ invariant footprint == \set_union(
      @    \all_fields(this), \set_union(
      @    \all_fields(values), \all_fields(keys)));
      @*/

    /*@ public normal_behaviour
      @  ensures m == \dl_mapEmpty();
      @  assignable \nothing;
      @*/
    public KIMapImpl() {
        this.count = 0;
        this.keys = new int[1024];
        this.values = new int[1024];
        //@ set m = \dl_mapEmpty();
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
      @  ensures (\forall int i; 0 <= i && i < count; 
      @              \result[i] == array[i]);
      @  ensures \result.length == newSize;
      @  assignable \nothing;
      @  helper
      @*/
    private int[] arrayClone(int[] array, int newSize) {
        int[] newArray = new int[newSize];
        /*@ loop_invariant 0 <= i && i <= count;
          @ loop_invariant (\forall int j; 0 <= j && j < i;
          @   newArray[j] == array[j]);
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
        int[] newkeys = arrayClone(keys, newSize);
        int[] newvalues = arrayClone(values, newSize);

        this.keys = newkeys;
        this.values = newvalues;

        //@ set footprint = \set_union(\all_fields(this), \set_union(\all_fields(values), \all_fields(keys)));
    }
          
    /*@ normal_behaviour 
      @  requires true;
      @  ensures \result >= -1;
      @  ensures \result < 0 ==> (\forall int i; 0 <= i && i < count; keys[i] != id);
      @  ensures \result >= 0 ==> (keys[\result] == id && \result < count);
      @  assignable \strictly_nothing; 
      @*/    
    private int posOfId(int id) {
        /*@ loop_invariant (\forall int k; 0 <= k && k < i; keys[k] != id);
          @ loop_invariant 0 <= i && i <= count;
          @ 
          @ decreases keys.length - i; 
          @ assignable \strictly_nothing;
          @*/
        for(int i = 0; i < count;  i++) {
            if(keys[i] == id) {
                return i;
            }            
        }
        return -1;
    }   


    /*@
      @ public normal_behavior 
      @  ensures \result == (\exists int i; 0 <= i && i < count; keys[i] == key);
      @  assignable \strictly_nothing;
      @*/
    public boolean contains(int key) {
        int pos = posOfId(key);
        return pos >= 0;
    }

    
    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; keys[i] == id);
      @  ensures (\exists int i; 0 <= i && i < count; \result == values[i] && keys[i] == id);
      @  assignable \strictly_nothing;
      @
      @ also public exceptional_behavior       
      @  requires (\forall int i; 0 <= i && i < count; keys[i] != id); 
      @  signals (IllegalArgumentException e) true;
      @  assignable \nothing;
      @*/
    public int get(int id) {
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
      @  ensures keys[\result] == id && values[\result] == pkey;
      @  // preservation of the remaining entries
      @  ensures m == \dl_mapUpdate(\old(m), id, pkey);
      @  assignable keys[*], values[*], count, m;
      @*/
    public int add(int id, int pkey) {
        int pos = posOfId(id);
        
        if(pos < 0) {
            pos = count;
            count ++;
        }
                
        keys[pos] = id;
        values[pos] = pkey;

        //@ set m = \dl_mapUpdate(m, id, pkey);
        
        return pos;
    }

    public void put(int key, int value) {
        if(count == keys.length) {
            resize(keys.length*2);
        }
        add(key, value);
    }
    
    public void del(int id) {
        int pos = posOfId(id);
        if(pos >= 0) {
            count --;
            if(count > 0 && pos != count) {
                keys[pos] = keys[count];
                values[pos] = values[count];
            }
            
            //@ set m = \dl_mapRemove(m, id);
            {}
        }        
    }
}
