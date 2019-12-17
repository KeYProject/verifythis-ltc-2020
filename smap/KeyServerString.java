/**
 * This is a simple backend for a verifying KeyServer. 
 *
 * This server uses integer values for the token, email and keys.
 * 
 * @author Alexander Weigl <weigl@kit.edu>
 * @version 1, 2019-12-17
 */
public class KeyServerString {
    private final KSMap storedKeys = new KSMapImpl();
    
    private final KSMap unconfirmedAdditionsEmail = new KSMapImpl();
    private final KSMap unconfirmedAdditionsKey = new KSMapImpl();

    private final KSMap unconfirmedDeletionsEmail = new KSMapImpl();
    private final KSMap unconfirmedDeletionsKey = new KSMapImpl();
    
    
    /*@ public normal_behaviour
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @ also 
      @  public exceptional_behavior       
      @  requires true;
      @  signals (Exception e) true;
      @*/
    public String get(String id) throws Exception {
        if(storedKeys.contains(id)){
            return storedKeys.get(id);
        }
        throw new Exception("Invalid key!");
    }


    /*@ public normal_behavior
      @  requires true;
      @  ensures \result.length >= 16;
      @  assignable \strictly_nothing;
      @*/
    private static /*@pure*/ String newTokenNumber() {
        return "00000000000000000000";//Math.random()*1000000/1000000;
    }

    //TODO weigl: How to handle overwritings of entry? Which method should throw
    //            an error or should we silently override?
  
    /*@ public normal_behavior
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @*/
    public String add(String id, String pkey) throws Exception {
        String tokenNumber = newTokenNumber();
        unconfirmedAdditionsEmail.put(tokenNumber, id);
        unconfirmedAdditionsEmail.put(tokenNumber, pkey);
        return tokenNumber;
    }
    
    
    /*@ public normal_behavior
      @  requires true;
      @  ensures true;
      @  assignable \strictly_nothing;
      @*/
    public void addConfirm(String tokenNumber) throws Exception {
        String id = unconfirmedAdditionsEmail.get(tokenNumber);
        String pkey = unconfirmedAdditionsKey.get(tokenNumber);
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
    public String del(String id) throws Exception {
        String token = newTokenNumber();
        String curKey = get(id);
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
    public void delConfirm(String tokenNumber) throws Exception {
        String id = unconfirmedDeletionsEmail.get(tokenNumber);
        String keyForDel = unconfirmedDeletionsKey.get(tokenNumber);

        if(keyForDel == get(id)) {//key did not change in the mean time
            storedKeys.del(id);
        }
    }
    
}
