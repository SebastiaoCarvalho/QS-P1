include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?
    ghost const max_val : nat
    ghost var content : set<nat>
    ghost var footprint : set<Ex3.Node>

    ghost function Valid() : bool 
    reads this, footprint, this.list, tbl
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
          && 
          tbl.Length == max_val + 1
          && 
          validTable(tbl, content)
        else 
          footprint == list.footprint
          &&
          content == list.content
          && 
          tbl.Length == max_val + 1
          &&
          validTable(tbl, content)
          &&
          list.Valid()
    }
      
    constructor (size : nat)
    ensures Valid() && this.content == {} && this.footprint == {} && this.max_val == size
    ensures fresh(this.tbl) && fresh(this.footprint)
    {
      tbl := new bool[size + 1] (_ => false);
      list := null;
      footprint := {};
      this.max_val := size;
      content := {};
    }


    method mem (v : nat) returns (b : bool)
    requires Valid()
    ensures b == (v in content)
    {
      if (v >= tbl.Length) {
        b := false;
        return;
      }
      if (tbl[v]) {
        b := true;
        return;
      }
      else {
        b := false;
        return;
      }
    }
    
    method add (v : nat) 
    requires Valid() && v <= max_val
    modifies this, this.tbl
    ensures Valid()
    ensures this.content == {v} + old(this.content)
    ensures this.footprint >= old(this.footprint)
    ensures this.footprint > old(this.footprint) ==>  fresh(this.footprint - old(this.footprint))
    ensures this.tbl == old(this.tbl)
    {
      if (this.list == null) {
        var n := new Ex3.Node(v);
        this.list := n;
        this.tbl[v] := true;
        this.content := {v};
        this.footprint := {n};
      }
      else {
        var condition := this.list.mem(v);
        if (! condition) {
          var n := this.list.add(v);
          this.list := n;
          this.tbl[v] := true;
          this.content := {v} + this.content;
          this.footprint := {n} + this.footprint;
        }
      }
    }

    method union(s : Set) returns (r : Set)
    requires Valid() && s.Valid()
    requires s.footprint !! this.footprint
    decreases footprint
    ensures fresh(r) && r.Valid()
    ensures r.content == s.content + this.content
    {
      var max_size := max(this.tbl.Length, s.tbl.Length);
      r := new Set(max_size);
      var cur1 := this.list;
      var list_aux : set<nat> := {};
      assert fresh(r.tbl);
      while (cur1 != null)
      invariant r.Valid()
      invariant cur1 != null ==> r.footprint !! cur1.footprint
      invariant fresh(r) && fresh(r.footprint) && fresh(r.tbl)
      invariant cur1 != null ==> cur1.Valid()
      invariant r.content == list_aux
      invariant cur1 != null ==> this.content == list_aux + cur1.content
      invariant cur1 == null ==> list_aux == this.content
      decreases if cur1 != null then cur1.footprint else {}
      {
        assert this.tbl != r.tbl;
        assert this != r;
        assert s.tbl != r.tbl;
        assert s != r;
        assert cur1 != r.list;
        r.add(cur1.val);
        list_aux := list_aux + {cur1.val};
        cur1 := cur1.next;
      }
      var cur2 := s.list;
      var list_aux2 : set<nat> := {};
      while (cur2 != null)
      invariant r.Valid()
      invariant r.content == list_aux2 + content
      invariant fresh(r) && fresh(r.footprint) && fresh(r.tbl)
      invariant cur2 != null ==> cur2.Valid()
      invariant cur2 != null ==> s.content == list_aux2 + cur2.content
      invariant cur2 == null ==> list_aux2 == s.content
      decreases if cur2 != null then cur2.footprint else {}
      {
        r.add(cur2.val);
        list_aux2 := list_aux2 + {cur2.val};
        cur2 := cur2.next;
      }
    }

    method inter(s : Set) returns (r : Set)
    requires Valid() && s.Valid()
    ensures fresh(r) && r.Valid()
    ensures r.content == s.content * this.content
    {
      var max_size := max(this.tbl.Length, s.tbl.Length);
      r := new Set(max_size);
      assert r.max_val == max_size;
      var cur1 := this.list;
      ghost var list_aux : set<nat> := {};
      while (cur1 != null)
      invariant r.Valid()
      invariant fresh(r) && fresh(r.footprint) && fresh(r.tbl)
      invariant cur1 != null ==> cur1.Valid()
      invariant r.content == list_aux * s.content
      invariant (cur1 != null) ==> (this.content == list_aux + cur1.content)
      invariant (cur1 == null) ==> (list_aux == this.content)
      decreases if cur1 != null then cur1.footprint else {}
      {
        var condition := s.mem(cur1.val);
        if (condition) {
          r.add(cur1.val);
        }
        list_aux := list_aux + {cur1.val};

        cur1 := cur1.next;
      }
    }

  }

  function validTable(tbl : array<bool>, content : set<nat>) : bool
  reads tbl
  {
    (forall k :: (k in content) ==> (0 <= k < tbl.Length))
    &&
    (forall k :: 0 <= k < tbl.Length ==> (tbl[k] == (k in content)))
  }

  function max(n1 : nat, n2 : nat) : nat
  {
    if (n1 > n2) then n1
    else n2
  }

}