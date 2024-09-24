
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : set<nat> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.val }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.val } + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat) 
    ensures this.Valid()
    ensures this.val == v
    ensures this.next == null
    ensures this.footprint == {this}
    ensures this.content == {v}
    {
      this.val := v;
      this.next := null;
      this.footprint := {this};
      this.content := {this.val};
    }

    method add(v : nat) returns (r : Node)
    requires Valid()
    ensures r.Valid()
    ensures r.next == this
    ensures r.val == v
    {
      r := new Node(v);
      r.next := this;
      r.footprint := {r} + this.footprint;
      r.content := {v} + this.content;
    }

    method mem(v : nat) returns (b : bool)
    decreases footprint
    requires Valid()
    ensures b == (v in content)
    {
      if (this.val == v) {
        b:= true;
        return;
      }
      else if (this.next != null) {
        b := this.next.mem(v);
        return;
      }
      else {
        b := false;
        return;
      }
    }

    method copy() returns (n : Node)
    requires Valid()
    ensures n.Valid() && Valid()
    ensures fresh(n.footprint)
    ensures n.content == this.content
    decreases footprint
    {
      n := new Node(this.val);
      if (this.next != null) {
        var aux := this.next.copy();
        n.next := aux;
        n.footprint := {n} + aux.footprint;
        n.content :=  {n.val} + aux.content;
      }
    }

  
  }

  
}
