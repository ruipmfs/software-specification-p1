function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1
method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{
  var len := r - l; // Calculate the length of the ret.
  ret := new int[len];  // Create the array ret with len
  var i := 0;

  while (i < len)
    invariant 0 <= i <= len 
    invariant forall k :: 0 <= k < i ==> ret[k] == a[l + k] // 'ret' should contain copied elements
    decreases len - i 
  {
    
    ret[i] := a[l + i]; // Copy the element from 'a' to 'ret' at the current index.
    i := i + 1;
  }
}


// Ex2
method swap(a: array<int>, i: int, j: int)
requires 0 <= i < a.Length && 0 <= j < a.Length
ensures old(a[i]) == a[j] && old(a[j]) == a[i]
ensures forall k:: 0 <= k < a.Length && k != i && k != j ==> old(a[k]) == a[k]
ensures multiset(a[..]) == multiset(old(a[..]))
modifies a
{
    a[i], a[j] := a[j], a[i];
}

method mergeArr(a: array<int>, l: int, m: int, r: int)
  requires 0 <= l < m < r <= a.Length
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a
{
  var leftSegment := copyArr(a, l, m);
  var rightSegment := copyArr(a, m, r);

  var i, j := 0, 0;

  while (i < leftSegment.Length || j < rightSegment.Length)
    invariant 0 <= i <= leftSegment.Length
    invariant 0 <= j <= rightSegment.Length
    invariant sorted(a[l..l+i+j])
    invariant forall k :: 0 <= k < l ==> a[k] == old(a[k])
    invariant forall k :: l+i+j <= k < a.Length ==> a[k] == old(a[k])
    decreases leftSegment.Length - i + rightSegment.Length - j
  {
    if (i < leftSegment.Length) {
      if (j >= rightSegment.Length || leftSegment[i] <= rightSegment[j]){
        a[l+i+j] := leftSegment[i];
        i := i + 1;
      }
    } else {
      a[l+i+j] := rightSegment[j];
      j := j + 1;
    }
  }
}


// Ex3
method sort (a : array<int>) 
  ensures sorted(a[..])
  modifies a 
{
  // ToDo
}

method mergeSort (a : array<int>) 
  ensures sorted(a[..])
  modifies a 
{
  var l, r := 0, a.Length-1;
  if l < r {
    var m := (l+r)/2;
    mergeSort(a[l..m]);
    mergeSort(a[m+1..l]);
    mergeArr(a, l, m ,r);
  }
}






