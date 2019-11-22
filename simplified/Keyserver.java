public class Keyserver {

    private final int[] emails = new int[1024];
    private final int[] keys = new int[1024];
    private int count;

    //@ invariant emails != null && keys != null;
    //@ invariant emails.length == keys.length;
    //@ invariant emails != keys;
    //@ invariant 0 <= count && count < emails.length;
    //@ invariant (\forall int i,j ; 0 <= i && i < j && j < count; emails[i] != emails[j]);


    /*@ normal_behaviour 
      @  requires true;
      @  ensures \result >= -1;
      @  ensures \result < 0 ==> (\forall int i; 0 <= i && i < count; emails[i] != id);
      @  ensures \result >= 0 ==> (emails[\result] == id && \result < count);
      @  assignable \strictly_nothing; 
      @*/    
    private int posOfId(int id) {
        /*@ loop_invariant (\forall int k; 0 <= k && k < i; emails[k] != id);
          @ loop_invariant 0 <= i && i <= count;
          @ 
          @ decreases emails.length - i; 
          @ assignable \strictly_nothing;
          @*/
        for(int i = 0; i < count;  i++) {
            if(emails[i] == id) {
                return i;
            }            
        }
        return -1;
    }   
    
    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures (\exists int i; 0 <= i && i < count; \result == keys[i] && emails[i] == id);
      @  assignable \strictly_nothing;
      @ also 
      @  public exceptional_behavior       
      @  requires (\forall int i; 0 <= i && i < emails.length; emails[i] != id); 
      @  signals (Exception e) true;
      @*/
    public int get(int id) throws Exception {
        int pos = posOfId(id);
        if(pos >= 0) 
            return keys[pos];
        else 
            throw new Exception();       
    }

  
    /*@ public normal_behaviour
      @  requires count < emails.length - 1;
      @  ensures 0 <= \result;
      @  ensures count == \old(count) && \result < count
      @      ||  count == \old(count) + 1 && \result == count - 1;
      @  ensures emails[\result] == id && keys[\result] == pkey;
      @  // preservation of the remaining entries
      @  ensures (\forall int i; 0<=i && i<count;
      @              (emails[i] == (i == \result ? id : \old(emails[i])))
      @           && (keys[i] == (i == \result ? pkey : \old(keys[i]))));
      @  assignable emails[*], keys[*], count;
      @*/
    public int add(int id, int pkey) throws Exception {
        int pos = posOfId(id);
        
        if(pos < 0) {
            pos = count;
            count ++;
        }
                
        emails[pos] = id;
        keys[pos] = pkey;
        return pos;
    }
    
    
    
    

    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures count == \old(count) - 1;
      @  ensures !(\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures (\forall int e; (\forall int k; e != id;
      @                 \old((\exists int i; 0 <= i && i < count; emails[i] == e && keys[i] == k))
      @            <==> (\exists int i; 0 <= i && i < count; emails[i] == e && keys[i] == k)));
      @  assignable emails[*], keys[*], count;
      @ also
      @ public normal_behaviour
      @  requires !(\exists int i; 0 <= i && i < count; emails[i] == id);
      @  assignable \strictly_nothing;
      @*/    
    public void del(int id) {

        int pos = posOfId(id);
        if(pos >= 0) {
            count --;
            if(count > 0 && pos != count) {
                emails[pos] = emails[count];
                keys[pos] = keys[count];
            }
        }
    }    
    
}
