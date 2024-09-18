datatype uop = Neg 
datatype bop = Plus | Minus 

datatype aexpr =
  Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)
 
datatype code = 
  | VarCode(seq<nat>)  
  | ValCode(nat)       
  | UnOpCode(uop)      
  | BinOpCode(bop)     

function Serialize(a : aexpr) : seq<code> 
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/
function Deserialize(cs : seq<code>) : seq<aexpr>
{
  DeserializeComplete(cs, [])
} 

function DeserializeComplete(cs : seq<code>, exps: seq<aexpr>) : seq<aexpr> 
{
  if (cs == []) then exps
  else DeserializeComplete(cs[1..], DeserializeAux(cs[0], exps))
}

function DeserializeAux(cd : code, exps : seq<aexpr>) : seq<aexpr>
{
  match cd {
    case VarCode(s) => [Var(s)] + exps
    case ValCode(i) => [Val(i)] + exps
    case UnOpCode(uop) => 
      if |exps| < 1 then []
      else [UnOp(uop, exps[0])] + exps[1..]
    case BinOpCode(bop) => 
      if |exps| < 2 then []
      else [BinOp(bop, exps[0], exps[1])] + exps[2..]
  }
}

/*
  Ex1.2
*/
lemma DeserializePropertyAux(e : aexpr, cs : seq<code>, exps: seq<aexpr>)
  ensures DeserializeComplete(Serialize(e) + cs, exps) == DeserializeComplete(cs, [ e ] + exps)
{
  match e {
    case Var(s) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(Var(s)) + cs, exps);
        == DeserializeComplete([VarCode(s)] + cs, exps);
        == {assert ([VarCode(s)] + cs)[1..] == cs;} DeserializeComplete(cs, DeserializeAux(VarCode(s), exps));
        == DeserializeComplete(cs, [Var(s)] + exps);
      }
    case Val(i) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(Val(i)) + cs, exps);
        == DeserializeComplete([ValCode(i)] + cs, exps);
        == {assert ([ValCode(i)] + cs)[1..] == cs;} DeserializeComplete(cs, DeserializeAux(ValCode(i), exps));
        == DeserializeComplete(cs, [Val(i)] + exps);
      }
    case UnOp(op, a1) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(UnOp(op, a1)) + cs, exps);
        == DeserializeComplete(Serialize(a1) + [UnOpCode(op)] + cs, exps);
        == {assert Serialize(a1) + [UnOpCode(op)] + cs == Serialize(a1) + ([UnOpCode(op)] + cs); } 
        DeserializeComplete(Serialize(a1) + ([UnOpCode(op)] + cs), exps);
        == {DeserializePropertyAux(a1, [UnOpCode(op)] + cs, exps);} DeserializeComplete([UnOpCode(op)] + cs, [a1] + exps);
        == DeserializeComplete(cs, DeserializeAux(UnOpCode(op), [a1] + exps));
        == DeserializeComplete(cs, [UnOp(op, a1)] + exps);
        == DeserializeComplete(cs, [e] + exps);
      }
    case BinOp(op, a1, a2) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(BinOp(op, a1, a2)) + cs, exps);
        == DeserializeComplete(Serialize(a2) + Serialize(a1) + [BinOpCode(op)] + cs, exps);
        == {assert Serialize(a2) + Serialize(a1) + [BinOpCode(op)] + cs == Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs); } 
        DeserializeComplete(Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs), exps);
        == {DeserializePropertyAux(a1, Serialize(a1) + [BinOpCode(op)] + cs, exps);}
        DeserializeComplete(Serialize(a1) + [BinOpCode(op)] + cs, [a2] + exps);
        == {assert Serialize(a1) + [BinOpCode(op)] + cs == Serialize(a1) + ([BinOpCode(op)] + cs);}
        DeserializeComplete(Serialize(a1) + ([BinOpCode(op)] + cs), [a2] + exps) ;
        == {DeserializePropertyAux(a1, [BinOpCode(op)] + cs, [a2] + exps);}
        DeserializeComplete([BinOpCode(op)] + cs, [a1] + ([a2] + exps));
        == {assert [a1] + ([a2] + exps) == [a1, a2] + exps;}
        DeserializeComplete([BinOpCode(op)] + cs, [a1, a2] + exps);
        == DeserializeComplete(cs, DeserializeAux(BinOpCode(op), [a1, a2] + exps));
        == DeserializeComplete(cs, [BinOp(op, a1, a2)] + exps);
        == DeserializeComplete(cs, [e] + exps);

      }
  }
}

lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [e]
{
  calc {
    Deserialize(Serialize(e));
    == {assert Serialize(e) + [] == Serialize(e);} DeserializeComplete(Serialize(e) + [], []);
    == {DeserializePropertyAux(e, [], []);} DeserializeComplete([], [e] + []);
    == DeserializeComplete([], [e]);
    == [e];
  }
}

/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{
  SerializeCodesComplete(cs, [])
}

function SerializeCodesComplete(cs : seq<code>, exprs : seq<nat>) : seq<nat>
{
  if (|cs| == 0) then exprs
  else SerializeCodesComplete(cs[1..], SerializeCodesAux(cs[0], exprs))
}

function SerializeCodesAux(c : code, exprs : seq<nat>) : seq<nat>
{
  match c {
    case VarCode(s) => [0] + [|s|] + s + exprs
    case ValCode(i) => [1, i]
    case UnOpCode(uop) => [SerializeUop(uop)] + exprs
    case BinOpCode(bop) => [SerializeBop(bop)] + exprs
  }
}

function SerializeUop(op : uop) : nat
{
  3
}

function SerializeBop(op : bop) : nat
{
  match op {
    case Plus => 4
    case Minus => 5
  }
}

function DeserializeCodes(ints : seq<nat>) : seq<code> 
{
  DeserializeCodesComplete(ints, [])
}

function DeserializeCodesComplete(ints : seq<nat>, exprs : seq<code>) : seq<code> 
{
  if (|ints| == 0) then exprs
  else match ints[0] {
      case 0 => if (|ints| < 2) then []
                else if (|ints| < 2 + ints[1]) then []
                else DeserializeCodesComplete(ints[(2 + ints[1])..], [VarCode(ints[2..(2 + ints[1])])] + exprs)
      case 1 => if (|ints| < 2) then []
                else DeserializeCodesComplete(ints[2..], [ValCode(ints[1])] + exprs)
      case 2 => DeserializeCodesComplete(ints[1..], [UnOpCode(Neg)] + exprs)
      case 4 => DeserializeCodesComplete(ints[1..], [BinOpCode(Plus)] + exprs)
      case 5 => DeserializeCodesComplete(ints[1..], [BinOpCode(Minus)] + exprs)
      case _ => []
  }
}

function DeserializeCodeVar(ints : seq<nat>, exprs : seq<code>) : seq<code>
{
  if (|ints| < 2) then []
  else if (|ints| < 2 + ints[1]) then []
  else DeserializeCodesComplete(ints[(2 + ints[1])..], [VarCode(ints[2..(2 + ints[1])])] + exprs)
}

function DeserializeCodeVal(ints : seq<nat>, exprs : seq<code>) : seq<code>
{
  if (|ints| < 2) then []
  else DeserializeCodesComplete(ints[2..], [ValCode(ints[1])] + exprs)
}
/*
  Ex1.4
*/
/*lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
}*/

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
  SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
  Deserialize(DeserializeCodes(nats))
}

/*
  Ex1.6
*/
/*lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
    
}*/