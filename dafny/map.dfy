
class Map  {

    var count: int

    var keys: array<string>
    var values: array<string>

    ghost var state: map<string, string>
    ghost var footprint: set<object>

    function Valid() : bool reads this, footprint {
      footprint == {this, values, keys} &&
        keys.Length == values.Length &&
        keys.Length > 0 &&
        keys != values &&
        0 <= count <= keys.Length &&
        (forall i,j :: 0 <= i < j < count ==> keys[i] != keys[j]) &&
        |state| == count && 
        (forall j :: 0 <= j < count ==> keys[j] in state && state[keys[j]] == values[j])
    }

    ghost method lemmaOnlyKeysInState(k : string)
      requires Valid()
      ensures k in state <==> exists i :: 0 <= i < count && keys[i] == k
    {
      var j := 0;
      while j < count
        invariant .......
      { j := j + 1; }
    }


    method Init()
      ensures state == map[]
      ensures Valid()
      ensures fresh(values) && fresh(keys)
      modifies this
    {
      this.count := 0;
      this.state := map[];
      this.keys := new string[1024];
      this.values := new string[1024];
      this.footprint := {this, values, keys};
    }

    method posOf(key: string) returns (pos: int)
      requires Valid()
      ensures -1 <= pos < count
      ensures pos == -1 <==> forall i :: 0 <= i < count ==> keys[i] != key
      ensures pos >= 0 ==> keys[pos] == key
    {
      var i := 0;
      while(i < count)
        invariant 0 <= i <= count
        invariant forall k :: 0 <= k < i ==> keys[k] != key
      {
        if keys[i] == key
        {
          return i;
        }
        i := i + 1;
      }
      return -1;
    }


    method contains(key: string) returns (result: bool)
      requires Valid()
      ensures result == (exists i :: 0 <= i < count && keys[i] == key)
    {
      var pos := posOf(key);
      result := pos >= 0;
    }

    method get(key: string) returns (value: string)
      requires Valid()
      requires exists i :: 0 <= i < count && key == keys[i]
      ensures  exists i :: 0 <= i < count && key == keys[i] && value == values[i]
    {
      assert exists i {: qwitness "wit1" } :: 0 <= i < count && key == keys[i];
         var wit1 : int;
         assume 0 <= wit1 < count && key == keys[wit1];
      
      assert key == keys[wit1];
      var pos := posOf(key);
      if pos == -1
      {
         assert forall i :: 0 <= i < count ==> keys[i] != key;
         assert keys[wit1] != key;
      }
      
      value := values[pos];
    }

    method add(key: string, value: string) returns (result: int)
      requires Valid()
      requires count <= keys.Length - 1
      ensures 0 <= result < count
      ensures keys == old(keys) && values == old(values)
      ensures (count == old(count) && result < count) ||
      (count == old(count) + 1 && result == count - 1)
      ensures state == state[key := value]
      ensures keys[result] == key && values[result] == value
      ensures Valid()
      modifies footprint
    {
      var pos := posOf(key);
      var hit := false;
      
      if pos < 0
      {
        pos := count;
        count := count + 1;
        hit := true;
      }

      keys[pos] := key;
      values[pos] := value;

      if hit
      {
        assert |state| == count-1;
        assert !(key in state);
      }
      state := state[key := value];
      if hit
      {
        assert |state| == count;
      }
      result := pos;        
    }
}
