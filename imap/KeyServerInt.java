/**
 * This is a simple backend for a verifying KeyServer. 
 *
 * This server uses integer values for the token, email and keys.
 * 
 * @author Alexander Weigl <weigl@kit.edu>
 * @version 1, 2019-12-10
 */
public class KeyServerInt {
    //@ invariant storedKeys.<inv>;
    private final KIMap storedKeys = new KIMapImpl();

    //@ invariant unconfirmedAdditionsEmail.<inv>;
    private final KIMap unconfirmedAdditionsEmail = new KIMapImpl();
    //@ invariant unconfirmedAdditionsKey.<inv>;
    private final KIMap unconfirmedAdditionsKey = new KIMapImpl();

    //@ invariant unconfirmedDeletionsEmail.<inv>;
    private final KIMap unconfirmedDeletionsEmail = new KIMapImpl();
    //@ invariant unconfirmedDeletionsKey.<inv>;
    private final KIMap unconfirmedDeletionsKey = new KIMapImpl();
    
    
    /*@ public normal_behaviour
      @  requires storedKeys.contains(id) == true;
      @  ensures \result == storedKeys.get(id);
      @  assignable \strictly_nothing;
      @ also 
      @  public exceptional_behavior       
      @  requires storedKeys.contains(id) != true;
      @  signals (Exception e) true;
      @*/
    public int get(int id) throws Exception {
        if(storedKeys.contains(id)){
            return storedKeys.get(id);
        }
        throw new Exception("Invalid key!");
    }


    /*@ public normal_behavior
      @  requires true;
      @  ensures 1000000 <= \result && result <= 9999999;
      @  assignable \strictly_nothing;
      @*/
    private static /*@pure*/ int newTokenNumber() {
        return (int) 0;//Math.random()*1000000/1000000;
    }

    //TODO weigl: How to handle overwritings of entry? Which method should throw
    //            an error or should we silently override?
  
    /*@ public normal_behavior
         requires \disjoint(this.*, unconfirmedAdditionsKey.footprint, 
                            storedKeys.footprint, unconfirmedDeletionsKey.footprint, 
                            unconfirmedDeletionsEmail.footprint, unconfirmedAdditionsEmail.footprint);

         //ensures 
         // \old(this.get(id)) == this.get(id);
         ensures 
           unconfirmedAdditionsEmail.get(\result) == id;
         ensures 
           unconfirmedAdditionsKey.get(\result) == pkey;
         ensures 
           unconfirmedDeletionsEmail.get(\result) == id;
         ensures 
           unconfirmedDeletionsKey.get(\result) == pkey;
         assignable \strictly_nothing;
      @*/
    public int add(int id, int pkey) throws Exception {
        int tokenNumber = newTokenNumber();
        unconfirmedAdditionsEmail.put(tokenNumber, id);
        unconfirmedAdditionsKey.put(tokenNumber, pkey);
        return tokenNumber;
    }
    
    
    /*@ public normal_behavior
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @*/
    public void addConfirm(int tokenNumber) throws Exception {
        int id = unconfirmedAdditionsEmail.get(tokenNumber);
        int pkey = unconfirmedAdditionsKey.get(tokenNumber);
        storedKeys.put(id, pkey);
    }
    

    /*@ public normal_behaviour
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @ also
      @ public normal_behaviour
      @  requires true; 
      @  assignable \strictly_nothing;
      @*/    
    public int del(int id) throws Exception {
        int token = newTokenNumber();
        int curKey = get(id);
        unconfirmedDeletionsEmail.put(token, id);
        unconfirmedDeletionsKey.put(token, curKey);
        return token;
    }


    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @ also
      @ public normal_behaviour
      @  requires true; 
      @  assignable \strictly_nothing;
      @*/    
    public void delConfirm(int tokenNumber) throws Exception {
        int id = unconfirmedDeletionsEmail.get(tokenNumber);
        int keyForDel = unconfirmedDeletionsKey.get(tokenNumber);

        if(keyForDel == get(id)) {//key did not change in the mean time
            storedKeys.del(id);
        }
    }
    
}
