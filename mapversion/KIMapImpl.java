public class KIMapImpl implements KIMap  {
    private int count = 0;
    private int[] keys = new int[1024],
        values = new int[1024];
    
    //@ invariant keys.length == values.length;
    //@ invariant keys != values;
    //@ invariant 0 <= count && count < keys.length;
    //@ invariant (\forall int i,j ; 0 <= i && i < j && j < count; keys[i] != keys[j]);

    
    //@ private instance ghost \locset footprint;
    
    /*@ represents m = compute(0);

      model_behavior 
      requires i >= 0 && i <= count; 
      ensures (\forall int j;  i <= j && j < count;
      \dl_mapGet(\result, keys[j]) == values[j]);
      assignable footprint;
      private model \map compute(int i) {
      return i == count ? \dl_mapEmpty
                        : \dl_mapUpdate(compute(i+1), 
                                        keys[i], values[i]);}

     */

    //@ accessible m : footprint;
    //@ accessible \inv : footprint;


    /*@ normal_behavior 
      requires newSize >= keys.length;
      requires newSize >= 0;
      ensures  keys.length == newSize;
      ensures  values.length == newSize;
      ensures  (\forall int i; 0 <= i && i < \old(values.length); 
      keys[i] == \old(keys[i]) && values[i] == \old(values[i]));
      assignable keys, values;
     */
    public void resize(int newSize) {
        int[] k = new int[newSize];
        int[] v = new int[newSize];
        /*@ loop_invariant
          (\forall int j; 0 <= j && j < i; k[j] == keys[j] && v[j] == values[j])
          && 0 <= i && i <= keys.length
          && k != null && v != null
          && keys != null && values != null
          && k.length == newSize
          && v.length == newSize;
        decreases values.length - i;
        assignable k[*], v[*]; 
        */
        for(int i = 0; i < values.length; i++) {
            k[i] = keys[i];
            v[i] = values[i];
        }
        values = v;
        keys = v;
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
      public normal_behavior 
      ensures \result == 
                (\exists int i; 0 <= i && i < keys.length; 
                keys[i] == key);

      assignable \strictly_nothing;
      @*/
    public boolean contains(int key) {
        int pos = posOfId(key);
        return pos >= 0;
    }

    
    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; keys[i] == id);
      @  ensures (\exists int i; 0 <= i && i < count; \result == values[i] && keys[i] == id);
      @  assignable \strictly_nothing;
      @ also 
      @  public exceptional_behavior       
      @  requires (\forall int i; 0 <= i && i < keys.length; keys[i] != id); 
      @  signals (Exception e) true;
      @*/
    public int get(int id) throws Exception {
        int pos = posOfId(id);
        if(pos >= 0) 
            return values[pos];
        else 
            throw new Exception();       
    }

  
    /*@ public normal_behaviour
      @  requires count < keys.length - 1;
      @  ensures 0 <= \result;
      @  ensures count == \old(count) && \result < count
      @      ||  count == \old(count) + 1 && \result == count - 1;
      @  ensures keys[\result] == id && values[\result] == pkey;
      @  // preservation of the remaining entries
      @  ensures (\forall int i; 0<=i && i<count;
      @              (keys[i] == (i == \result ? id : \old(keys[i])))
      @           && (values[i] == (i == \result ? pkey : \old(values[i]))));
      @  assignable keys[*], values[*], count;
      @*/
    public int add(int id, int pkey) throws Exception {
        int pos = posOfId(id);
        
        if(pos < 0) {
            pos = count;
            count ++;
        }
                
        keys[pos] = id;
        values[pos] = pkey;
        return pos;
    }

    public void put(int key, int value) {
        try{
            add(key, value);
        } catch(Exception e) {

        }
    }
    

    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; keys[i] == id);
      @  ensures count == \old(count) - 1;
      @  ensures !(\exists int i; 0 <= i && i < count; keys[i] == id);
      @  ensures (\forall int e; (\forall int k; e != id;
      @                 \old((\exists int i; 0 <= i && i < count; keys[i] == e && values[i] == k))
      @            <==> (\exists int i; 0 <= i && i < count; keys[i] == e && values[i] == k)));
      @  assignable keys[*], values[*], count;
      @ also
      @ public normal_behaviour
      @  requires !(\exists int i; 0 <= i && i < count; keys[i] == id);
      @  assignable \strictly_nothing;
      @*/    
    public void del(int id) {
        int pos = posOfId(id);
        if(pos >= 0) {
            count --;
            if(count > 0 && pos != count) {
                keys[pos] = keys[count];
                values[pos] = values[count];
            }
        }
    }
}
