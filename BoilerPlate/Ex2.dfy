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
  var cur := l;

  while ((i < leftSegment.Length || j < rightSegment.Length) && cur < r)
    invariant 0 <= i <= leftSegment.Length
    invariant 0 <= j <= rightSegment.Length
    invariant l <= cur <= r
    invariant cur == l+i+j
    invariant sorted(leftSegment[..]) && sorted(rightSegment[..])
    invariant 0 <= i < leftSegment.Length && cur > l ==> leftSegment[i] >= a[cur -1]
    invariant  cur > l && 0 <= j < rightSegment.Length  ==> rightSegment[j] >= a[cur -1] 
    invariant sorted(a[l..cur])
    invariant forall k :: 0 <= k < l ==> a[k] == old(a[k])
    invariant forall k :: cur <= k < a.Length ==> a[k] == old(a[k])
    decreases r - cur
  {
    if (i < leftSegment.Length && (j >= rightSegment.Length || leftSegment[i] <= rightSegment[j])) {
      a[cur] := leftSegment[i];
      i := i + 1;
    } else {
      a[cur] := rightSegment[j];
      j := j + 1;
    }
    cur := cur + 1;
  }
}


method mergeSort(a: array<int>)
  ensures sorted(a[..])
  modifies a
{
  mergeSortAux(a, 0, a.Length);
}

method mergeSortAux(a: array<int>, l: int, r: int)
  requires 0 <= l <= r <= a.Length
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a
  decreases r - l
{
  if (r - l <= 1) {
    return;
  }

  var m : int := l + (r - l) / 2;

  mergeSortAux(a, l, m);
  mergeSortAux(a, m, r);
  mergeArr(a, l, m, r);
}