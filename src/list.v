Require Import List.

Check 1::2::3::nil.

Compute
  map (fun x => x + 2) (1::2::3::nil).
