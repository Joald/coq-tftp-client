Load client.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlIntConv.

Extraction Blacklist String Int List Nat.

Extraction "Client"
           coq_init
           coq_process_packet
           n_of_int
           int_of_n
           pos_of_int
           int_of_pos
           nat_of_int
           int_of_nat.

Separate Extraction
         BinNat BinNums BinInt BinPos (* to jest potrzebne do camlcoq *)
         .
