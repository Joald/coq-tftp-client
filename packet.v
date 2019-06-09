Require Import ZArith.

Inductive packet_type : Set := RRQ | WRQ | DATA | ACK | ERROR.

Definition type_to_int (type: packet_type) : positive :=
  match type with  
    | RRQ   => 1
    | WRQ   => 2
    | DATA  => 3
    | ACK   => 4
    | ERROR => 5
  end.


