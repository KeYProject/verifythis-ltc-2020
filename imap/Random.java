class Random {

    // That is somewhat untrue, assuming that the entire heap is the
    // state. ... There should be some explicit seed. Later ...
    
    /*@ public normal_behaviour
      @  assigns \strictly_nothing;
      @*/
    public native static int nextInt();
}
