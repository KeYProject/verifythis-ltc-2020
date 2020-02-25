/**
 * Simplified Java version of the HAGRID OpenPGP server
 *( https://gitlab.com/hagrid-keyserver ). Manages the access to public keys.
 * 
 */
public class Keyserver {
    private int MAXUSERS = 1024;
    private final int[] emails = new int[MAXUSERS];
    private final int[] keys = new int[MAXUSERS];
    private final int[] codes = new int[MAXUSERS];
    private final int[] unconfirmedKeys = new int[MAXUSERS];
    private final int[] requestType = new int[MAXUSERS];
    private int count;
    private static final int REQUESTTYPE_ADD = 0;
    private static final int REQUESTTYPE_REMOVE = 1;


    //ruling out aliasing between arrays
    //@ invariant emails != keys && emails != codes && emails != unconfirmedKeys;
    //@ invariant emails != requestType;
    //@ invariant keys != codes && keys != unconfirmedKeys;
    //@ invariant keys != requestType;
    //@ invariant codes != unconfirmedKeys && codes != requestType;
    //@ invariant unconfirmedKeys != requestType;

    // all arrays are non-null and have the same length (the # users)
    //@ invariant emails != null && keys != null && codes != null;
    //@ invariant unconfirmedKeys != null && requestType != null;
    //@ invariant emails.length == MAXUSERS && keys.length == MAXUSERS;
    //@ invariant codes.length == MAXUSERS && unconfirmedKeys.length == MAXUSERS;
    //@ invariant requestType.length == MAXUSERS;
    
    // number of users is bounded
    //@ invariant 0 <= count && count <= MAXUSERS;
    
    //emails are unique
    //@ invariant (\forall int i,j ; 0 <= i && i < j && j < count; emails[i] != emails[j]);

    /**
     * Returns the array index where the info of the user with the specified
     * id/email is stored.
     *
     * @param id
     *            the id/email of the user
     * @return the array index where user info is stored
     */
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
    
    /**
     * Returns the key with the specified email address.
     * 
     * @param id
     *            the id/email of the user
     * @return the key of the user
     * @throws Exception
     *             if the specified user id/email does not exist
     */
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

    /**
     * Stores request to add the given key for the specified user. The key still
     * needs to be confirmed with {@link #addConfirm(int, int)}. Does nothing if
     * the specified user does not exist.
     * 
     * @param id
     *            id the id/email of the user
     * @param pkey
     *            the key to be added after confirmation
     * @return the array index where the key will be stored
     */
    /*@ public normal_behaviour
      @  requires count < MAXUSERS;
      @  ensures 0 <= \result;
      @  ensures count == \old(count) && \result < count
      @      ||  count == \old(count) + 1 && \result == count - 1;
      @  ensures emails[\result] == id && unconfirmedKeys[\result] == pkey && codes[\result]>0;
      @  ensures requestType[\result] == REQUESTTYPE_ADD;
      @  // preservation of the other entries
      @  ensures (\forall int i; 0<=i && i<count;
      @              (emails[i] == (i == \result ? id : \old(emails[i])))
      @           && (unconfirmedKeys[i] == (i == \result ? pkey : \old(unconfirmedKeys[i])))
      @           && (i != \result ==> (codes[i] == \old(codes[i])))
      @           && (i != \result ==> (requestType[i] == \old(requestType[i]))));
      @  assignable emails[*], unconfirmedKeys[*], codes[*], requestType[*], count;
      @*/
    public int addRequest(int id, int pkey) {
        int pos = posOfId(id);
        
        if(pos < 0) {
            pos = count;
            count ++;
        }
        
        emails[pos] = id;
        codes[pos] = 1; // TODO: Random positive number?
        unconfirmedKeys[pos] = pkey;
        requestType[pos] = REQUESTTYPE_ADD;
        return pos;
    }

    /**
     * Stores the key previously supplied to {@link #addRequest(int, int)} if
     * the given code matches the secret confirmation code generated in
     * {@code addRequest} for the given user. If it does not match: does
     * nothing.
     * 
     * @param id
     *            the id/email of the user
     * @param code
     *            the confirmation code for the add operation
     * @return the index where the key is stored, or -1 if nothing is done.
     */
    /*@ public normal_behaviour
      @  requires code > 0 && (\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code && requestType[i] == REQUESTTYPE_ADD));
      @  ensures 0 <= \result;
      @  ensures emails[\result] == id && keys[\result] == \old(unconfirmedKeys[\result]) && codes[\result]==0;
      @  // preservation of the other entries
      @  ensures (\forall int i; 0<=i && i<count; (i != \result ==>
      @              (keys[i] == \old(keys[i])) && (codes[i] == \old(codes[i]))));
      @  assignable keys[*], codes[*];
      @ also
      @ public normal_behaviour
      @  requires code <= 0 || !(\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code && requestType[i] == REQUESTTYPE_ADD));
      @  ensures \result == -1;
      @  assignable \strictly_nothing;
      @*/
    public int addConfirm(int id, int code) {
        int pos = posOfId(id);
        
        if(pos >= 0 && code > 0 && code == codes[pos] && requestType[pos] == REQUESTTYPE_ADD) {
            // code confirmed, store key
            keys[pos] = unconfirmedKeys[pos];
            codes[pos] = 0;
        } else {
            pos = -1;
        }

        return pos;
    }

    /**
     * Stores request to remove the given key for the specified user. The
     * removal still needs to be confirmed with {@link #delConfirm(int, int)}.
     * Does nothing if the specified user does not exist.
     * 
     * @param id
     *            the id/email of the user
     * @return the array index where the key will be stored. -1 if the user does
     *         not exist
     */
    /*@ public normal_behaviour
      @  requires (\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures requestType[\result] == REQUESTTYPE_REMOVE;
      @  ensures (\forall int i; 0<=i && i<count;
      @              (emails[i] == (i == \result ? id : \old(emails[i])))
      @           && (i != \result ==> (codes[i] == \old(codes[i])))
      @           && (i != \result ==> (requestType[i] == \old(requestType[i]))));
      @  ensures codes[\result] > 0;
      @  assignable codes[*], requestType[*];
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
                requestType[pos] = REQUESTTYPE_REMOVE;
            }
        }
        
        return pos;
    }

    /**
     * Removes the key as previously requested in {@link #delRequest(int)} if
     * the given code matches the secret confirmation code generated in
     * {@code delRequest} for the given user. Does nothing if there is no match.
     * 
     * @param id
     *            the id/email of the user
     * @param code
     *            the confirmation code for the removal operation
     */
    /*@ public normal_behaviour
      @  requires code > 0 && (\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code && requestType[i] == REQUESTTYPE_REMOVE));
      @  ensures count == \old(count) - 1;
      @  ensures !(\exists int i; 0 <= i && i < count; emails[i] == id);
      @  ensures (\forall int e; (\forall int k; e != id;
      @                 \old((\exists int i; 0 <= i && i < count; emails[i] == e && keys[i] == k))
      @            <==> (\exists int i; 0 <= i && i < count; emails[i] == e && keys[i] == k)));
      @  assignable emails[*], keys[*], count;
      @ also
      @ public normal_behaviour
      @  requires code <= 0 || !(\exists int i; 0 <= i && i < count; (emails[i] == id && codes[i] == code && requestType[i] == REQUESTTYPE_REMOVE));
      @  assignable \strictly_nothing;
      @*/    
    public void delConfirm(int id, int code) {

        int pos = posOfId(id);
        if(pos >= 0 && code > 0 && code == codes[pos] && requestType[pos] == REQUESTTYPE_REMOVE) {
            //code confirmed, remove key
            count --;
            if(count > 0 && pos != count) {
                emails[pos] = emails[count];
                keys[pos] = keys[count];
            }
        }
    }
}
