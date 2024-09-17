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
  Deserialize(cs, [])
} 

function Deserialize(cs : seq<code>, exps: seq<aexpr>) : seq<aexpr> 
{
  if (cs == []) then []
  else Deserialize(cs[1..], DeserializeAux(cs[0], exps))
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
  ensures Deserialize(Serialize(e) + cs, exps) == Deserialize(cs, [ e ] + exps)
{
  match e {
    case Var(s) =>
      calc {
        Deserialize(Serialize(e) + cs, exps);
        == Deserialize(Serialize(Var(s)) + cs, exps);
        == Deserialize([VarCode(s)] + cs, exps);
        == {assert ([VarCode(s)] + cs)[1..] == cs;} Deserialize(cs, DeserializeAux(VarCode(s), exps));
        == Deserialize(cs, [Var(s)] + exps);
      }
    case Val(i) =>
      calc {
        Deserialize(Serialize(e) + cs, exps);
        == Deserialize(Serialize(Val(i)) + cs, exps);
        == Deserialize([ValCode(i)] + cs, exps);
        == {assert ([ValCode(i)] + cs)[1..] == cs;} Deserialize(cs, DeserializeAux(ValCode(i), exps));
        == Deserialize(cs, [Val(i)] + exps);
      }
    case UnOp(op, a1) =>
      calc {
        Deserialize(Serialize(e) + cs, exps);
        == Deserialize(Serialize(UnOp(op, a1)) + cs, exps);
        == Deserialize(Serialize(a1) + [UnOpCode(op)] + cs, exps);
        == {assert Serialize(a1) + [UnOpCode(op)] + cs == Serialize(a1) + ([UnOpCode(op)] + cs); } 
        Deserialize(Serialize(a1) + ([UnOpCode(op)] + cs), exps);
        == {DeserializeProperty(a1, [UnOpCode(op)] + cs, exps);} Deserialize([UnOpCode(op)] + cs, [a1] + exps);
        == Deserialize(cs, DeserializeAux(UnOpCode(op), [a1] + exps));
        == Deserialize(cs, [UnOp(op, a1)] + exps);
        == Deserialize(cs, [e] + exps);
      }
    case BinOp(op, a1, a2) =>
      calc {
        Deserialize(Serialize(e) + cs, exps);
        == Deserialize(Serialize(BinOp(op, a1, a2)) + cs, exps);
        == Deserialize(Serialize(a2) + Serialize(a1) + [BinOpCode(op)] + cs, exps);
        == {assert Serialize(a2) + Serialize(a1) + [BinOpCode(op)] + cs == Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs); } 
        Deserialize(Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs), exps);
        == {DeserializeProperty(a1, Serialize(a1) + [BinOpCode(op)] + cs, exps);}
        Deserialize(Serialize(a1) + [BinOpCode(op)] + cs, [a2] + exps);
        == {assert Serialize(a1) + [BinOpCode(op)] + cs == Serialize(a1) + ([BinOpCode(op)] + cs);}
        Deserialize(Serialize(a1) + ([BinOpCode(op)] + cs), [a2] + exps) ;
        == {DeserializeProperty(a1, [BinOpCode(op)] + cs, [a2] + exps);}
        Deserialize([BinOpCode(op)] + cs, [a1] + ([a2] + exps));
        == {assert [a1] + ([a2] + exps) == [a1, a2] + exps;}
        Deserialize([BinOpCode(op)] + cs, [a1, a2] + exps);
        == Deserialize(cs, DeserializeAux(BinOpCode(op), [a1, a2] + exps));
        == Deserialize(cs, [BinOp(op, a1, a2)] + exps);
        == Deserialize(cs, [e] + exps);

      }
  }
}

lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == e
{

}

/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{
  if (|cs| == 0) then []
  else {
    cs 
  }
}

function SerializeCodesAux(c : code) : seq<nat>
{
  match c {
    case VarCode(s) => [0] + [|s|] + s
    case ValCode(i) => [1, i]
    case UnOpCode(uop) => 
      [SerializeUop(uop)] + SerializeCode
    case BinOpCode(bop) => 
      if |exps| < 2 then []
      else [BinOp(bop, exps[0], exps[1])] + exps[2..]
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

/* function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
}*/


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
/*function FullSerialize(e : aexpr) : seq<nat> {
 
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
}*/

/*
  Ex1.6
*/
/*lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
    
}*/