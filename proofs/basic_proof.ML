(* Basic proof script to test the test harness *)
let rec factorial n =
  if n <= 1 then 1 else n * factorial (n - 1);;
