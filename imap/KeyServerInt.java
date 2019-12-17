/**
 * This is a simple backend for a verifying KeyServer. 
 *
 * This server uses integer values for the token, email and keys.
 * 
 * @author Alexander Weigl <weigl@kit.edu>
 * @version 1, 2019-12-10
 */
public class KeyServerInt {
    private final KIMap storedKeys = new KIMapImpl();
    
    private final KIMap unconfirmedAdditionsEmail = new KIMapImpl();
    private final KIMap unconfirmedAdditionsKey = new KIMapImpl();

    private final KIMap unconfirmedDeletionsEmail = new KIMapImpl();
    private final KIMap unconfirmedDeletionsKey = new KIMapImpl();
    
    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @ also 
      @  public exceptional_behavior       
      @  requires true;
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
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @*/
    public int add(int id, int pkey) throws Exception {
        int tokenNumber = newTokenNumber();
        unconfirmedAdditionsEmail.put(tokenNumber, id);
        unconfirmedAdditionsEmail.put(tokenNumber, pkey);
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
