public class Math {
    
    /*@
      @ requires true;
      @ ensures 0 <= \result && \result < range;
      @ assignable \strictly_nothing;
     */
    public native static final int random(int range);
}
