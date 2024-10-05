method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  ensures b <==> (forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j])
  ensures !b <==> (exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j && arr[i] == arr[j])
{
  var i := 0; 
  b := true; 

  while (i < arr.Length)
  invariant 0 <= i <= arr.Length
  invariant forall k, m :: 0 <= k < i && 0 <= m < i && k != m ==> arr[k] != arr[m]
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length) 
    invariant 0 <= j <= arr.Length
    invariant forall k :: 0 <= k < j && k != i ==> arr[k] != arr[i]
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }
}

method Max(nat1 : nat, nat2 : nat) returns (z: nat)
ensures nat1 > nat2 ==> z == nat1
ensures nat2 >= nat1 ==> z == nat2
{
  if (nat1 > nat2){
    z := nat1;
  }
  else {
    z := nat2;
  }
  return;
} 


method noRepetitionsLinear(arr : array<nat>) returns (b: bool)
  ensures b <==> (forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j])
  ensures !b <==> (exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j && arr[i] == arr[j])
{
  var max : nat := 0;
  var i := 0;
  
  while (i < arr.Length)
  invariant 0 <= i <= arr.Length
  invariant forall k :: 0 <= k < i ==> arr[k] <=  max
  {
    max := Max(max, arr[i]);
    i := i + 1;
  }

  var table := new bool[max + 1] (_ => false);

  i:= 0;
  b := true;
  while (i < arr.Length)
  invariant 0 <= i <= arr.Length
  invariant forall k :: 0 <= k < i ==> table[arr[k]]
  invariant forall k :: (0 <= k <= max && table[k]) ==> (exists j :: 0 <= j < i && arr[j] == k)
  invariant forall k, m :: 0 <= k < i && 0 <= m < i && k != m ==> arr[k] != arr[m]
  {
    if (table[arr[i]]) {
      b := false;
      return;
    }
    table[arr[i]] := true;
    i := i + 1;
  }
  b := true;
  return;
}
