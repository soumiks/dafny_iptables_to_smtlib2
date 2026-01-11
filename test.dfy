method Max(a: int, b: int) returns (res: int)
  // Fill in the 'ensures' clauses here to prove the two points above!
  ensures res >= a && res >= b
  ensures res == a || res == b
{
  if a > b {
    res := a;
  } else {
    res := b;
  }
}

method Main() {
  var a := 10;
  var b := 20;
  var m := Max(a, b);
  
  // Because of your 'ensures' clauses, Dafny knows this is true:
  assert m == 20; 
  assert m >= a;
  assert m >= b;
  
  print m;
}
