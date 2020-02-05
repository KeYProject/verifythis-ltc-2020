public class Keyserver {
    private static int MAXUSERS = 1024;
    private final int[] emails = new int[MAXUSERS];
    private final int[] keys = new int[MAXUSERS];
    private final int[] codes = new int[MAXUSERS];
    private final int[] unconfirmedKeys = new int[MAXUSERS];
    private int count;

    //ruling out aliasing between arrays
    //@ invariant emails != keys && emails != codes && emails != unconfirmedKeys;
    //@ invariant keys != codes && keys != unconfirmedKeys;
    //@ invariant codes != unconfirmedKeys;

    //@ invariant emails != null && keys != null && codes != null && unconfirmedKeys != null;
    //@ invariant emails.length == MAXUSERS && keys.length == MAXUSERS && codes.length == MAXUSERS && unconfirmedKeys.length == MAXUSERS;
    //@ invariant 0 <= count && count <= MAXUSERS;
    //@ invariant (\forall int i,j ; 0 <= i && i < j && j < count; emails[i] != emails[j]);


    /*@ normal_behaviour 
      @  requires true;
      @  ensures \result >= -1;
      @  ensures \result == -1 ==> (\forall int i; 0 <= i && i < count; emails[i] != id);
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
      @  requires count < MAXUSERS;
      @  ensures 0 <= \result;
      @  ensures count == \old(count) && \result < count
      @      ||  count == \old(count) + 1 && \result == count - 1;
      @  ensures emails[\result] == id && unconfirmedKeys[\result] == pkey && codes[\result]>0;
      @  // preservation of the other entries
      @  ensures (\forall int i; 0<=i && i<count;
      @              (emails[i] == (i == \result ? id : \old(emails[i])))
      @           && (unconfirmedKeys[i] == (i == \result ? pkey : \old(unconfirmedKeys[i])))
      @           && (i != \result ==> (codes[i] == \old(codes[i]))));
      @  assignable emails[*], unconfirmedKeys[*], codes[*], count;
      @*/
    public int addRequest(int id, int pkey) throws Exception {
        int pos = posOfId(id);
        
        if(pos < 0) {
            pos = count;
            count ++;
        }
                
        emails[pos] = id;
        codes[pos] = 1; // TODO: Random positive number?
        unconfirmedKeys[pos] = pkey;
        return pos;
    }




  
    /*@ public normal_behaviour
	  @ requires code > 0 && (\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code));
      @  ensures 0 <= \result;
      @  ensures emails[\result] == id && keys[\result] == \old(unconfirmedKeys[\result]) && codes[\result]==0;
      @  // preservation of the other entries
      @  ensures (\forall int i; 0<=i && i<count; (i != \result ==>
      @              (keys[i] == \old(keys[i])) && (codes[i] == \old(codes[i]))));
      @  assignable keys[*], codes[*];
      @ also
      @ public normal_behaviour
      @  requires code <= 0 || !(\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code));
	  @  ensures \result == -1;
      @  assignable \strictly_nothing;
      @*/
    public int addConfirm(int id, int code) throws Exception {
        int pos = posOfId(id);
        
        if(pos >= 0 && code > 0 && code == codes[pos]) {
            // code confirmed, store key
            keys[pos] = unconfirmedKeys[pos];
	        codes[pos] = 0;
	    } else {
            pos = -1;
		}

        return pos;
    }
    
    

    
    

    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures (\forall int i; 0 <= i && i < count; (i != \result ==>
      @              (codes[i] == \old(codes[i]))));
	  @  ensures codes[\result] > 0;
      @  assignable codes[*];
      @ also
      @ public normal_behaviour
      @  requires !(\exists int i; 0 <= i && i < count; emails[i] == id);
	  @  ensures \result == -1;
      @  assignable \strictly_nothing;
      */    
    public int delRequest(int id) {
        int pos = posOfId(id);
        if(pos >= 0) {
            if(count > 0 && pos != count) {
                codes[pos] = 1; // Random positive number?
            }
        }
		
		return pos;
    }
    
    
    
    

    /*@ public normal_behaviour
	  @  requires code > 0 && (\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code));
      @  ensures count == \old(count) - 1;
      @  ensures !(\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures (\forall int e; (\forall int k; e != id;
      @                 \old((\exists int i; 0 <= i && i < count; emails[i] == e && keys[i] == k))
      @            <==> (\exists int i; 0 <= i && i < count; emails[i] == e && keys[i] == k)));
      @  assignable emails[*], keys[*], count;
      @ also
      @ public normal_behaviour
	  @  requires code <= 0 || !(\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code));
      @  assignable \strictly_nothing;
      @*/    
    public void delConfirm(int id, int code) {

        int pos = posOfId(id);
        if(pos >= 0 && code > 0 && code == codes[pos]) {
            //code confirmed, remove key
            count --;
            if(count > 0 && pos != count) {
                emails[pos] = emails[count];
                keys[pos] = keys[count];
            }
        }
    }
    
}
