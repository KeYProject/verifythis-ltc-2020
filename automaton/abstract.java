/*@ model */ enum State { REGISTERED, CONFIRMED }

/**
 * We use Java records (version 15+) for modelling of mathematical tuples.
 * We consider these tuples are immutable and heap-indepent. Also, we assume
 * a proper definition for .equals/.hashcode (based on symbolical equality).
 */
/*@ model */ record Entry(
    State s,  
    /*@non_null*/ String email,
    /*@non_null*/ String publicKey,
    /*@nullable*/ String confirmCode) {
}

interface Hagrid {
    //@ ghost List<Entry> entries;

    /*@ invariant dupsFree = 
        (\forall idx1,entry1 in \old(entries);
            (\forall idx2,entry2 in \old(entries);
                idx1!=idx2 ==> entry1.key!=entry2.key))
    */


    /*@ public normal_behavior 
        requires  Entry(_, email, _, _) !in entries;
         {* short form for 
          * (\forall int i; 0 <= i <= seqLen(entries); 
          *   seqGet(entries, i).email != email);
          *}
        ensures Entry(email, publicKey, \result) in entries;
        ensures \forall entry in \old(entries); entry in entries;
    */
    public String register(String email, String publicKey);

    /*@ public normal_behavior 
        forall String publicKey; 
        requires  Entry(CONFIRMED, email, publicKey, _) in entries;         
        ensures entries == \old(entries);
        ensures \result == publicKey;
    */
    public String get(String email);
    

    /*@ public normal_behavior 
        forall String publicKey, String email; 
        requires Entry(REGISTERED, email, publicKey, cc) in entries;
        ensures  Entry(CONFIRMED, email, publicKey, _) in entries;
        ensures (\forall entry in \old(entries);
                        entry.confirmCode != cc; 
                        entry in entries);
    */
    public String confirm(String cc);


    /*@ public normal_behavior 
        ensures Entry(_, email, _, _) !in entries;         
        ensures (\forall entry in \old(entries);
                        entry.email != email; 
                        entry in entries);
    */
    public void revoke(String email);    
}

class TheRealHagrid implements Hagrid {
    // refinement of the operations
}
